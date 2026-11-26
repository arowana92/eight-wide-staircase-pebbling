"""Replay each project module in a separate stock leanchecker process under lake env."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def replay(file):
    module = '.'.join(file.relative_to(ROOT).with_suffix('').parts)
    subprocess.run(['leanchecker', module], cwd=ROOT, check=True)
    print(f'Passed {module}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1, help='number of checker processes')
    args = parser.parse_args()
    files = sorted((ROOT / 'Staircase').rglob('*.lean'))
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for _ in pool.map(replay, files):
            pass
    print(f'Passed all {len(files)} project modules.', flush=True)


if __name__ == '__main__':
    main()
