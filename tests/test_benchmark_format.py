# test_benchmark_format.py
import subprocess
import os

def test_output_format():
    """Test that Rust outputs in correct format for Python to parse"""
    print("Testing Rust benchmark output format...")
    
    env = os.environ.copy()
    env['NP'] = '2'
    env['NV'] = '50'
    env['T'] = '1024'
    
    # Run the Rust benchmark
    result = subprocess.run(
        ['cargo', 'test', 'test_hc_voting', '--release', '--', '--nocapture'],
        env=env,
        capture_output=True,
        text=True
    )
    
    print("Sample output lines:")
    print("-" * 50)
    
    # Look for timing lines
    for line in result.stdout.split('\n'):
        if 'Time elapsed in' in line:
            print(line)
        if 'Size of' in line:
            print(line)
        if 'HC Voting Parameters' in line:
            print(line)
    
    print("-" * 50)
    
    # Check format
    expected_formats = [
        'Time elapsed in generate h_{i,x}:',
        'Size of generate h_{i,x}:',
        'Time elapsed in tallying:'
    ]
    
    all_good = True
    for expected in expected_formats:
        if expected not in result.stdout:
            print(f"❌ Missing: {expected}")
            all_good = False
        else:
            print(f"✅ Found: {expected}")
    
    if all_good:
        print("\n✅ All formats correct! Python script should work.")
    else:
        print("\n❌ Some formats missing. Fix Rust output format.")

if __name__ == "__main__":
    test_output_format()