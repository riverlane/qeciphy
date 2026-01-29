# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2025 Riverlane Ltd.

import sys
import json

def get_nested(cfg, keys):
    for key in keys:
        if isinstance(cfg, dict) and key in cfg:
            cfg = cfg[key]
        else:
            return None
    return cfg

def main():
    if len(sys.argv) < 3:
        print("Usage: read_cfg.py <config.json> <field>")
        sys.exit(1)

    cfg_file = sys.argv[1]
    field_path = sys.argv[2]

    # Support for keys like profiles.zcu216.synth.top
    keys = field_path.split('.')

    with open(cfg_file, 'r') as f:
        cfg = json.load(f)

    value = get_nested(cfg, keys)
    if value is None:
        sys.exit(1)

    # Print value(s), one per line if list, else print directly
    if isinstance(value, list):
        # Special handling for pre_setup_hooks - output as space-separated list
        if field_path.endswith('.pre_setup_hooks'):
            print(' '.join(value))
        else:
            for v in value:
                # If it's a dict (e.g. hooks), print as JSON string
                if isinstance(v, dict):
                    print(json.dumps(v))
                else:
                    print(v)
    elif isinstance(value, dict):
        print(json.dumps(value))
    else:
        print(value)

if __name__ == "__main__":
    main()