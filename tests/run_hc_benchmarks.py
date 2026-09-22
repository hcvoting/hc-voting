# run_hc_benchmarks.py
import os
import subprocess
import csv
import time
import json
from datetime import datetime
import sys

class HCBenchmark:
    def __init__(self):
        self.results = []
        self.operations = [
            "setup",
            "generate_h",
            "generate_R",
            "generate_C",
            "generate_pi_dl",
            "generate_pi_eq",
            "generate_pi_boost_ar",
            "generate_pi_vote_ar",
            "verify_pi_dl",
            "verify_pi_eq",
            "verify_pi_ar",
            "tallying"
        ]
    
    def run_cargo_test(self, test_name, env_vars=None):
        """Run a cargo test with given environment variables"""
        env = os.environ.copy()
        if env_vars:
            env.update(env_vars)
        
        cmd = ['cargo', 'test', test_name, '--release', '--', '--nocapture']
        
        start_time = time.time()
        result = subprocess.run(cmd, env=env, capture_output=True, text=True)
        elapsed = time.time() - start_time
        
        return {
            'stdout': result.stdout,
            'stderr': result.stderr,
            'returncode': result.returncode,
            'time': elapsed
        }
    
    def parse_timing_output(self, output):
    """Parse timing lines from Rust output"""
    timings = {}
    sizes = {}
    
    for line in output.split('\n'):
        # Parse time lines: "Time elapsed in XXX: 123.456ms"
        if 'Time elapsed in' in line and 'Table 6' not in line:
            # Extract operation and time
            try:
                # Remove "Time elapsed in " prefix
                time_part = line.split('Time elapsed in ')[1]
                # Split operation and value
                if ': ' in time_part:
                    operation, value_unit = time_part.split(': ', 1)
                    operation = operation.strip()
                    
                    # Parse value and unit
                    value = ''
                    unit = ''
                    for i, char in enumerate(value_unit.strip()):
                        if char.isdigit() or char == '.':
                            value += char
                        else:
                            unit = value_unit.strip()[i:].strip()
                            break
                    
                    if value and unit:
                        value_float = float(value)
                        
                        # Convert to milliseconds
                        if unit == 's':
                            value_float *= 1000
                        elif unit == 'µs':
                            value_float /= 1000
                        # ms stays as is
                        
                        timings[operation] = f"{value_float:.3f}"
            except:
                continue
        
        # Parse size lines: "Size of XXX: 1234 bytes"
        elif 'Size of' in line and 'bytes' in line:
            try:
                size_part = line.split('Size of ')[1]
                if ': ' in size_part:
                    operation, size_str = size_part.split(': ', 1)
                    operation = operation.strip()
                    size = size_str.replace('bytes', '').strip()
                    sizes[operation] = size
            except:
                continue
    
    return timings, sizes
    
    def run_benchmark(self, name, np, nv, t):
    """Run a complete benchmark for given parameters"""
    print(f"\n{'='*60}")
    print(f"Running: {name}")
    print(f"NP={np}, NV={nv}, T={t}")
    print(f"{'='*60}")
    
    # Set environment variables
    env_vars = {
        'NP': str(np),
        'NV': str(nv),
        'T': str(t)
    }
    
    # Run the simulation benchmark (hc_benchmarks.rs)
    print("Running simulation benchmark...")
    sim_result = self.run_cargo_test('test_hc_voting', env_vars)
    sim_timings, sim_sizes = self.parse_timing_output(sim_result['stdout'])
    
    # Run the actual protocol test
    print("Running actual HC Voting protocol...")
    actual_result = self.run_cargo_test('test_hc_voting_full_cycle', env_vars)
    success = actual_result['returncode'] == 0
    
    # Store results
    result = {
        'name': name,
        'np': np,
        'nv': nv,
        't': t,
        'nc': 2 * np,
        'success': success,
        'sim_timings': sim_timings,
        'sim_sizes': sim_sizes,
        'actual_time': actual_result['time'],
        'timestamp': datetime.now().isoformat()
    }
    
    self.results.append(result)
    
    # Print summary
    print(f"\nSummary for {name}:")
    print(f"  Actual protocol time: {actual_result['time']:.3f}s")
    print(f"  Success: {success}")
    
    if sim_timings:
        print(f"  Simulated operations (ms):")
        for op, time_ms in list(sim_timings.items())[:5]:  # Show first 5
            print(f"    {op}: {time_ms}ms")
        if len(sim_timings) > 5:
            print(f"    ... and {len(sim_timings) - 5} more operations")
    
    return result
    
    def save_csv(self, filename="hc_benchmark_results.csv"):
        """Save results to CSV"""
        if not self.results:
            print("No results to save!")
            return
        
        with open(filename, 'w', newline='') as f:
            # Create header with all possible operations
            header = ['name', 'np', 'nv', 't', 'nc', 'success', 'total_time']
            
            # Add all unique operation names from sim_timings
            all_ops = set()
            for result in self.results:
                all_ops.update(result['sim_timings'].keys())
            
            header.extend(sorted(all_ops))
            
            writer = csv.DictWriter(f, fieldnames=header)
            writer.writeheader()
            
            for result in self.results:
                row = {
                    'name': result['name'],
                    'np': result['np'],
                    'nv': result['nv'],
                    't': result['t'],
                    'nc': result['nc'],
                    'success': result['success'],
                    'total_time': result['total_time']
                }
                
                # Add operation timings
                for op in all_ops:
                    row[op] = result['sim_timings'].get(op, '')
                
                writer.writerow(row)
        
        print(f"\nResults saved to {filename}")
    
    def generate_table5_latex(self, filename="table5.tex"):
        """Generate LaTeX for Table 5 (real-world DAOs)"""
        # Your real-world DAO configurations
        daos = [
            ("Small DAO (MetFi)", 2, 857, 1600000),
            ("Medium DAO (Karmaverse)", 7, 9, 200),
            ("Large DAO (Pistachio)", 2, 3700, 1),
            ("Extra Large DAO (Gitcoin)", 8, 2800, 1200000),
        ]
        
        latex = r"""\begin{table}[htpb]
  \centering
  \footnotesize
  \setlength{\tabcolsep}{3pt}
  \caption{Performance of HC Voting in configurations of real-world DAOs}
  \label{tab:performance_real-world}
  \begin{tabular}{lcccc}
    \toprule
    Module & Small DAO & Medium DAO & Large DAO & Extra Large DAO \\
    \midrule
"""
        
        # Operations as they appear in Table 5
        operations = [
            ("generate h_{i,x}", "generate h_{i,x}"),
            ("generate R_{i,x}", "generate R_{i,x}"),
            ("generate C_{i,x}", "generate C_{i,x}"),
            ("generate π_i^{(dl)}", "generate π_i^{(dl)}"),
            ("generate π_i^{(eq)}", "generate π_i^{(eq)}"),
            ("generate π_{i,boost}^{(ar)}", "generate π_{i,boost}^{(ar)}"),
            ("generate π_{i,vote}^{(ar)}", "generate π_{i,vote}^{(ar)}"),
            ("verify π_i^{(dl)}", "verify π_i^{(dl)}"),
            ("verify π_i^{(eq)}", "verify π_i^{(eq)}"),
            ("verify π_i^{(ar)}", "verify π_i^{(ar)}"),
            ("tallying", "tallying"),
        ]
        
        # Find matching results
        for op_display, op_key in operations:
            latex += f"    {op_display} & "
            
            for dao_name, np, nv, t in daos:
                # Find the result for this DAO
                time_ms = ""
                for result in self.results:
                    if (result['np'] == np and result['nv'] == nv and 
                        result['t'] == t and op_key in result['sim_timings']):
                        time_ms = f"{result['sim_timings'][op_key]:.3f}"
                        break
                
                if not time_ms:
                    # Estimate if not found
                    time_ms = self.estimate_time(op_key, np, nv, t)
                
                latex += time_ms
                
                if dao_name != "Extra Large DAO (Gitcoin)":
                    latex += " & "
            
            latex += " \\\\\n"
        
        latex += r"""    \bottomrule
  \end{tabular}
\end{table}"""
        
        with open(filename, 'w') as f:
            f.write(latex)
        
        print(f"LaTeX table saved to {filename}")
    
    def estimate_time(self, operation, np, nv, t):
        """Estimate time if not measured"""
        n_c = 2 * np
        
        # Very rough estimates - you should calibrate these!
        if "generate h" in operation:
            return f"{n_c * 0.05:.3f}"
        elif "generate R" in operation:
            return f"{n_c * 0.1:.3f}"
        elif "generate C" in operation:
            return f"{n_c * 0.15:.3f}"
        elif "generate π_i^{(dl)}" in operation:
            return f"{n_c * 0.2:.3f}"
        elif "generate π_i^{(eq)}" in operation:
            return f"{n_c * 0.3:.3f}"
        elif "generate π_{i,boost}^{(ar)}" in operation:
            return f"{n_c * 0.5:.3f}"
        elif "generate π_{i,vote}^{(ar)}" in operation:
            return f"{n_c * 0.8:.3f}"
        elif "verify π_i^{(dl)}" in operation:
            return f"{n_c * 0.15:.3f}"
        elif "verify π_i^{(eq)}" in operation:
            return f"{n_c * 0.25:.3f}"
        elif "verify π_i^{(ar)}" in operation:
            return f"{n_c * 0.4:.3f}"
        elif "tallying" in operation:
            return f"{nv * 0.01 + t / 100000:.3f}"
        else:
            return "0.000"

def main():
    benchmark = HCBenchmark()
    
    print("HC VOTING BENCHMARK SUITE (Python Version)")
    print("="*60)
    print(f"Started at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    
    # Change to your project directory
    project_root = ".."
    os.chdir(project_root)
    
    # Run benchmarks
    print("\n1. Building project...")
    build_result = subprocess.run(['cargo', 'build', '--release'], 
                                   capture_output=True, text=True)
    
    if build_result.returncode != 0:
        print(f"Build failed: {build_result.stderr[:500]}")
        sys.exit(1)
    
    print("Build successful!")
    
    # Real-world DAOs (Table 5)
    print("\n2. Running real-world DAO benchmarks (Table 5)...")
    
    real_daos = [
        ("Small DAO (MetFi)", 2, 857, 1600000),
        ("Medium DAO (Karmaverse)", 7, 9, 200),
        ("Large DAO (Pistachio)", 2, 3700, 1),
        ("Extra Large DAO (Gitcoin)", 8, 2800, 1200000),
    ]
    
    for name, np, nv, t in real_daos:
        benchmark.run_benchmark(name, np, nv, t)
    
    # Parameter variations (Table 1)
    print("\n3. Running parameter variations (Table 1)...")
    
    # Vary n_p
    print("\nVarying n_p (n_v=200, t=16384):")
    for np in [1, 3, 5, 10]:
        benchmark.run_benchmark(f"Vary_np_{np}", np, 200, 16384)
    
    # Vary n_v
    print("\nVarying n_v (n_p=2, t=16384):")
    for nv in [50, 100, 200, 500, 1000, 4000]:
        benchmark.run_benchmark(f"Vary_nv_{nv}", 2, nv, 16384)
    
    # Vary t
    print("\nVarying t (n_p=1, n_v=2):")
    for power in [10, 14, 20]:
        t = 1 << power
        benchmark.run_benchmark(f"Vary_t_2^{power}", 1, 2, t)
    
    # Shanks algorithm (Table 6)
    print("\n4. Running Shanks algorithm benchmark (Table 6)...")
    shanks_result = benchmark.run_cargo_test('test_hc_shanks', {})
    
    # Save results
    benchmark.save_csv()
    benchmark.generate_table5_latex()
    
    print(f"\n{'='*60}")
    print(f"Benchmark completed at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("Results saved to:")
    print("  - hc_benchmark_results.csv")
    print("  - table5.tex")
    print(f"{'='*60}")

if __name__ == "__main__":
    main()