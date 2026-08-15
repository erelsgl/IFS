import numpy as np

def compute_utility_r2(p, q, t):
    """Computes the separable ell_t utility in pure R^2: -sum(|p_j - q_j|^t)."""
    return -np.sum(np.abs(p - q) ** t)

def compute_ifs1_r2(p, t, n):
    """
    Computes IFS1 (Maximin) in pure R^2.
    The agent chooses a share vector d_i (with ||d_i|| <= 1/n or bounded coordinates),
    and the adversary dumps the remaining (n-1)/n budget into a chosen coordinate direction.
    """
    p = np.array(p, dtype=float)
    # Agent's best local allocation in R^2: moving 1/n towards the peak in each coordinate,
    # bounded by the peak itself (the R^2 analogue of water-filling).
    d_i = np.zeros(2)
    for j in range(2):
        d_i[j] = np.sign(p[j]) * min(abs(p[j]), 1.0 / n)
        
    # Adversary chooses a coordinate axis j to shift by (n-1)/n to hurt the agent most
    ifs1_val = float('inf')
    for j in range(2):
        d_minus_i = np.zeros(2)
        # The adversary pushes away from the peak to maximize distance
        d_minus_i[j] = -np.sign(p[j]) * ((n - 1.0) / n)
        
        q = d_i + d_minus_i
        util = compute_utility_r2(p, q, t)
        if util < ifs1_val:
            ifs1_val = util
            
    return ifs1_val

def compute_ifs2_r2(p, t, n):
    """
    Computes IFS2 (Minimax) in pure R^2.
    The adversary commits to a directional move of (n-1)/n first, 
    and the agent best-responds with a 1/n move.
    """
    p = np.array(p, dtype=float)
    
    ifs2_val = float('inf')
    for j in range(2):
        y = np.zeros(2)
        y[j] = -np.sign(p[j]) * ((n - 1.0) / n)
        
        # Agent best responds to the adversary's disruption vector y
        adjusted_peaks = p - y
        x = np.zeros(2)
        for k in range(2):
            x[k] = np.sign(adjusted_peaks[k]) * min(abs(adjusted_peaks[k]), 1.0 / n)
            
        q = x + y
        util = compute_utility_r2(p, q, t)
        if util < ifs2_val:
            ifs2_val = util
            
    return ifs2_val
