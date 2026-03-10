"""Unified model interface for benchmark evaluation.

Each adapter calls its provider's API, records token usage, and computes cost.
"""

from __future__ import annotations

import os
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field

import yaml


@dataclass
class GenerateResult:
    """Result of a single model generation call."""
    text: str
    input_tokens: int
    output_tokens: int
    cost_usd: float
    latency_s: float
    raw_response: dict = field(default_factory=dict, repr=False)
    sampling_params: dict = field(default_factory=dict)  # temperature, seed, top_p etc.


class ModelAdapter(ABC):
    """Abstract base for all model adapters."""

    def __init__(self, config: dict):
        self.model_id = config["model_id"]
        self.input_price = config["input_price_per_m"]
        self.output_price = config["output_price_per_m"]
        self.max_tokens = config.get("max_tokens", 8192)
        self.temperature = config.get("temperature", 0.0)
        self.config = config

    def compute_cost(self, input_tokens: int, output_tokens: int) -> float:
        return (input_tokens * self.input_price + output_tokens * self.output_price) / 1_000_000

    @abstractmethod
    def generate(self, messages: list[dict], **kwargs) -> GenerateResult:
        """Generate a completion from the model.

        Args:
            messages: List of {"role": "system"|"user"|"assistant", "content": str}
            **kwargs: Provider-specific overrides (max_tokens, temperature, etc.)

        Returns:
            GenerateResult with text, token counts, cost, and latency.
        """


class ClaudeAdapter(ModelAdapter):
    """Anthropic Claude models via anthropic SDK."""

    def __init__(self, config: dict):
        super().__init__(config)
        try:
            import anthropic
        except ImportError:
            raise ImportError("pip install anthropic")
        api_key = os.environ.get(config.get("api_key_env", "ANTHROPIC_API_KEY"))
        if not api_key:
            raise ValueError(f"Set {config.get('api_key_env', 'ANTHROPIC_API_KEY')} env var")
        self.client = anthropic.Anthropic(api_key=api_key)

    def generate(self, messages: list[dict], **kwargs) -> GenerateResult:
        # Separate system message from conversation
        system_text = ""
        conv_messages = []
        for m in messages:
            if m["role"] == "system":
                system_text += m["content"] + "\n"
            else:
                conv_messages.append(m)

        max_tokens = kwargs.get("max_tokens", self.max_tokens)
        temperature = kwargs.get("temperature", self.temperature)

        start = time.monotonic()
        response = self.client.messages.create(
            model=self.model_id,
            max_tokens=max_tokens,
            temperature=temperature,
            system=system_text.strip() if system_text else None,
            messages=conv_messages,
        )
        latency = time.monotonic() - start

        text = response.content[0].text if response.content else ""
        input_tokens = response.usage.input_tokens
        output_tokens = response.usage.output_tokens
        cost = self.compute_cost(input_tokens, output_tokens)

        return GenerateResult(
            text=text,
            input_tokens=input_tokens,
            output_tokens=output_tokens,
            cost_usd=cost,
            latency_s=latency,
            raw_response={"stop_reason": response.stop_reason},
            sampling_params={
                "temperature": temperature,
                "max_tokens": max_tokens,
                "top_p": None,  # Anthropic API does not expose top_p
                "seed": None,   # Anthropic API does not support seed
                "provider": "anthropic",
                "model_id": self.model_id,
            },
        )


class OpenAIAdapter(ModelAdapter):
    """OpenAI models (GPT-4o, o3-mini) via openai SDK."""

    def __init__(self, config: dict):
        super().__init__(config)
        try:
            from openai import OpenAI
        except ImportError:
            raise ImportError("pip install openai")
        api_key = os.environ.get(config.get("api_key_env", "OPENAI_API_KEY"))
        if not api_key:
            raise ValueError(f"Set {config.get('api_key_env', 'OPENAI_API_KEY')} env var")
        self.client = OpenAI(api_key=api_key)

    def generate(self, messages: list[dict], **kwargs) -> GenerateResult:
        max_tokens = kwargs.get("max_tokens", self.max_tokens)
        temperature = kwargs.get("temperature", self.temperature)
        seed = kwargs.get("seed", self.config.get("seed"))
        top_p = kwargs.get("top_p", self.config.get("top_p", 1.0))

        api_kwargs = dict(
            model=self.model_id,
            messages=messages,
            max_tokens=max_tokens,
            temperature=temperature,
            top_p=top_p,
        )
        if seed is not None:
            api_kwargs["seed"] = seed

        start = time.monotonic()
        response = self.client.chat.completions.create(**api_kwargs)
        latency = time.monotonic() - start

        choice = response.choices[0]
        text = choice.message.content or ""
        input_tokens = response.usage.prompt_tokens
        output_tokens = response.usage.completion_tokens
        cost = self.compute_cost(input_tokens, output_tokens)

        return GenerateResult(
            text=text,
            input_tokens=input_tokens,
            output_tokens=output_tokens,
            cost_usd=cost,
            latency_s=latency,
            raw_response={
                "finish_reason": choice.finish_reason,
                "system_fingerprint": getattr(response, "system_fingerprint", None),
            },
            sampling_params={
                "temperature": temperature,
                "max_tokens": max_tokens,
                "top_p": top_p,
                "seed": seed,
                "provider": "openai",
                "model_id": self.model_id,
            },
        )


class OpenAICompatibleAdapter(ModelAdapter):
    """OpenAI-compatible APIs (DeepSeek, Qwen, local via ollama/vllm)."""

    def __init__(self, config: dict):
        super().__init__(config)
        try:
            from openai import OpenAI
        except ImportError:
            raise ImportError("pip install openai")
        api_key = os.environ.get(config.get("api_key_env", ""), "sk-placeholder")
        api_base = config.get("api_base", "http://localhost:11434/v1")
        self.client = OpenAI(api_key=api_key, base_url=api_base)

    def generate(self, messages: list[dict], **kwargs) -> GenerateResult:
        max_tokens = kwargs.get("max_tokens", self.max_tokens)
        temperature = kwargs.get("temperature", self.temperature)
        seed = kwargs.get("seed", self.config.get("seed"))
        top_p = kwargs.get("top_p", self.config.get("top_p", 1.0))

        api_kwargs = dict(
            model=self.model_id,
            messages=messages,
            max_tokens=max_tokens,
            temperature=temperature,
            top_p=top_p,
        )
        if seed is not None:
            api_kwargs["seed"] = seed

        start = time.monotonic()
        response = self.client.chat.completions.create(**api_kwargs)
        latency = time.monotonic() - start

        choice = response.choices[0]
        text = choice.message.content or ""
        usage = response.usage
        input_tokens = usage.prompt_tokens if usage else 0
        output_tokens = usage.completion_tokens if usage else 0
        cost = self.compute_cost(input_tokens, output_tokens)

        return GenerateResult(
            text=text,
            input_tokens=input_tokens,
            output_tokens=output_tokens,
            cost_usd=cost,
            latency_s=latency,
            raw_response={"finish_reason": choice.finish_reason},
            sampling_params={
                "temperature": temperature,
                "max_tokens": max_tokens,
                "top_p": top_p,
                "seed": seed,
                "provider": self.config.get("provider", "openai_compatible"),
                "model_id": self.model_id,
            },
        )


class GoogleAdapter(ModelAdapter):
    """Google Gemini models via google-genai SDK."""

    def __init__(self, config: dict):
        super().__init__(config)
        try:
            from google import genai
        except ImportError:
            raise ImportError("pip install google-genai")
        api_key = os.environ.get(config.get("api_key_env", "GOOGLE_API_KEY"))
        if not api_key:
            raise ValueError(f"Set {config.get('api_key_env', 'GOOGLE_API_KEY')} env var")
        self.client = genai.Client(api_key=api_key)

    def generate(self, messages: list[dict], **kwargs) -> GenerateResult:
        from google.genai import types

        # Convert messages to Gemini format
        system_text = ""
        contents = []
        for m in messages:
            if m["role"] == "system":
                system_text += m["content"] + "\n"
            elif m["role"] == "user":
                contents.append(types.Content(role="user", parts=[types.Part(text=m["content"])]))
            elif m["role"] == "assistant":
                contents.append(types.Content(role="model", parts=[types.Part(text=m["content"])]))

        max_tokens = kwargs.get("max_tokens", self.max_tokens)
        temperature = kwargs.get("temperature", self.temperature)

        gen_config = types.GenerateContentConfig(
            max_output_tokens=max_tokens,
            temperature=temperature,
            system_instruction=system_text.strip() if system_text else None,
        )

        start = time.monotonic()
        response = self.client.models.generate_content(
            model=self.model_id,
            contents=contents,
            config=gen_config,
        )
        latency = time.monotonic() - start

        text = response.text or ""
        usage = response.usage_metadata
        input_tokens = usage.prompt_token_count if usage else 0
        output_tokens = usage.candidates_token_count if usage else 0
        cost = self.compute_cost(input_tokens, output_tokens)

        return GenerateResult(
            text=text,
            input_tokens=input_tokens,
            output_tokens=output_tokens,
            cost_usd=cost,
            latency_s=latency,
            raw_response={},
            sampling_params={
                "temperature": temperature,
                "max_tokens": max_tokens,
                "top_p": None,  # Gemini uses top_p but not passed through here yet
                "seed": None,   # Gemini supports seed but not configured
                "provider": "google",
                "model_id": self.model_id,
            },
        )


# --- Factory ---

_PROVIDER_MAP = {
    "anthropic": ClaudeAdapter,
    "openai": OpenAIAdapter,
    "google": GoogleAdapter,
    "deepseek": OpenAICompatibleAdapter,
    "openai_compatible": OpenAICompatibleAdapter,
    "local": OpenAICompatibleAdapter,
}


def create_adapter(model_name: str, models_config: dict | None = None) -> ModelAdapter:
    """Create a ModelAdapter from config.

    Args:
        model_name: Key in models.yaml (e.g., "claude-sonnet-4.6")
        models_config: Pre-loaded config dict. If None, loads from default path.
    """
    if models_config is None:
        config_path = os.path.join(os.path.dirname(__file__), "..", "config", "models.yaml")
        with open(config_path) as f:
            models_config = yaml.safe_load(f)

    if model_name not in models_config["models"]:
        available = ", ".join(models_config["models"].keys())
        raise ValueError(f"Unknown model '{model_name}'. Available: {available}")

    config = models_config["models"][model_name]
    provider = config.get("provider", "openai_compatible")

    adapter_cls = _PROVIDER_MAP.get(provider)
    if adapter_cls is None:
        raise ValueError(f"Unknown provider '{provider}'. Available: {list(_PROVIDER_MAP.keys())}")

    return adapter_cls(config)
