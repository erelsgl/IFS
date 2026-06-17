import numpy as np

def water_filling(initial_peaks, budget, tol=1e-12):
    """
    Implements the strongly polynomial water-filling algorithm (Theorem 3.5).
    Allocates the budget by greedily reducing the highest deficits.
    """
    m = len(initial_peaks)
    x = np.zeros(m)
    b = budget
    
    while b > tol:
        deficits = initial_peaks - x
        max_deficit = np.max(deficits)
        
        # Find all components achieving the maximum deficit
        J = np.where(np.abs(deficits - max_deficit) < tol)[0]
        num_J = len(J)
        
        if num_J == m:
            # All deficits are equal, distribute remaining budget equally
            x += b / m
            b = 0.0
            break
        else:
            x1 = max_deficit
            remaining_deficits = [deficits[k] for k in range(m) if k not in J]
            x2 = np.max(remaining_deficits)
            
            # Check if budget is exhausted before reaching the next highest deficit
            if b <= (x1 - x2) * num_J + tol:
                x[J] += b / num_J
                b = 0.0
                break
            else:
                inc = x1 - x2
                x[J] += inc
                b -= inc * num_J
                
    return x

def compute_utility(p, q, t):
    """Computes the separable ell_t utility function: -sum(|p_j - q_j|^t)."""
    return -np.sum(np.abs(p - q) ** t)

def validate_inputs(p, t, n):
    """Common helper to validate inputs for IFS computations."""
    p = np.array(p, dtype=float)
    assert np.isclose(np.sum(p), 1.0), "Peak distribution must sum to 1."
    assert n >= 2, "Number of agents must be at least 2."
    assert t >= 1, "t parameter must be >= 1."
    return p

def compute_ifs1(p, t, n):
    """
    Computes the IFS1 value (Maximin) for a single agent (Theorem 3.5).
    
    The agent commits to an allocation first. The adversary responds by dumping 
    all remaining budget into the alternative that hurts the agent most.
    """
    p = validate_inputs(p, t, n)
    m = len(p)
    
    # 1. Compute optimal d_i for the agent using water-filling
    d_i = water_filling(p, 1.0 / n)
    
    # 2. Evaluate worst-case adversarial vertex choice
    ifs1_val = float('inf')
    for j in range(m):
        d_minus_i = np.zeros(m)
        d_minus_i[j] = (n - 1.0) / n
        q = d_i + d_minus_i
        util = compute_utility(p, q, t)
        if util < ifs1_val:
            ifs1_val = util
            
    return ifs1_val

def compute_ifs2(p, t, n):
    """
    Computes the IFS2 value (Minimax) for a single agent (Theorem 3.7).
    
    The adversary commits to an allocation vertex first. The agent observes 
    this move and computes their best response via water-filling.
    """
    p = validate_inputs(p, t, n)
    m = len(p)
    
    # Evaluate minimax value by minimizing over the adversary's vertices
    ifs2_val = float('inf')
    for j in range(m):
        # Adversary allocates all remaining budget to alternative j
        y = np.zeros(m)
        y[j] = (n - 1.0) / n
        
        # Modify the peaks for water-filling to find best-response x
        adjusted_peaks = p - y
        x = water_filling(adjusted_peaks, 1.0 / n)
        
        # Combined outcome distribution
        q = x + y
        util = compute_utility(p, q, t)
        if util < ifs2_val:
            ifs2_val = util
            
    return ifs2_val

# --- Main Demonstration Program ---
if __name__ == "__main__":
    print("="*60)
    print("Individual Fair Share (IFS) Calculator (Theorems 3.5 & 3.7)")
    print("="*60)
    
    # Example 1: Replicating Paper's Example 3.4 (n=2, m=2, t=1, peak=[0.5, 0.5])
    p1 = [0.5, 0.5]
    t1 = 1
    n1 = 2
    
    ifs1_ex1 = compute_ifs1(p1, t1, n1)
    ifs2_ex1 = compute_ifs2(p1, t1, n1)
    
    print(f"Example 1 (Paper Example 3.4) -> n={n1}, m={len(p1)}, t={t1}, peak={p1}")
    print(f"  IFS1 (Maximin): {ifs1_ex1:.4f}  [Expected: -0.5, maps to 0.75 overlap]")
    print(f"  IFS2 (Minimax): {ifs2_ex1:.4f}  [Expected:  0.0, maps to 1.00 overlap]")
    print("-" * 60)
    
    # Example 2: Higher dimensions and t=2 (Euclidean distance metrics)
    p2 = [0.6, 0.3, 0.1]
    t2 = 2
    n2 = 3
    
    ifs1_ex2 = compute_ifs1(p2, t2, n2)
    ifs2_ex2 = compute_ifs2(p2, t2, n2)
    
    print(f"Example 2 -> n={n2}, m={len(p2)}, t={t2}, peak={p2}")
    print(f"  IFS1 (Maximin): {ifs1_ex2:.4f}")
    print(f"  IFS2 (Minimax): {ifs2_ex2:.4f}")
    print(f"  Observation Verification: IFS1 <= IFS2 is {ifs1_ex2 <= ifs2_ex2}")
    print("="*60)
