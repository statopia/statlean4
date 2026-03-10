#!/usr/bin/env python3
"""
Quick search tool for Shao Mathematical Statistics theorem catalog.
Usage:
  python3 scripts/search_shao.py "Cochran"
  python3 scripts/search_shao.py "1.5"
  python3 scripts/search_shao.py "Lemma"
"""

import yaml
import sys
import re

def load_catalog():
    with open('theme/input/shao_theorem_catalog.yaml') as f:
        return yaml.safe_load(f)

def search(query):
    catalog = load_catalog()
    query_lower = query.lower()
    
    results = []
    
    for ch_num in sorted(catalog['chapters'].keys()):
        ch = catalog['chapters'][ch_num]
        
        for stmt_type in ['theorems', 'propositions', 'lemmas', 'corollaries']:
            if stmt_type in ch:
                for item in ch[stmt_type]:
                    # Match on number or name
                    if (query_lower in item['num'].lower() or 
                        query_lower in item['name'].lower() or
                        query_lower == stmt_type.rstrip('s')):
                        results.append({
                            'chapter': ch_num,
                            'type': stmt_type.rstrip('s').title(),
                            'num': item['num'],
                            'name': item['name'],
                            'page': item['page']
                        })
    
    if not results:
        print(f"No results for: {query}")
        return
    
    # Sort by chapter, then by number
    results.sort(key=lambda x: (x['chapter'], 
                                [int(p) for p in x['num'].split('.')]))
    
    for r in results:
        print(f"Ch.{r['chapter']} {r['type']} {r['num']}: {r['name']} (p.{r['page']})")

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: python3 scripts/search_shao.py <query>")
        print("Examples:")
        print("  - Theorem number: '1.5'")
        print("  - Name keyword: 'Cochran'")
        print("  - Statement type: 'Lemma'")
        sys.exit(1)
    
    search(sys.argv[1])
