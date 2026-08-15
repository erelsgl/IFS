import numpy as np
import matplotlib.pyplot as plt
from compute_ifs_r2 import compute_ifs1_r2, compute_ifs2_r2, compute_utility_r2

def plot_ifs_boundary_pure_r2(p, n, t, mode='IFS1', resolution=300):
    """
    Plots the IFS boundary for an unconstrained peak p in the pure R^2 plane.
    X-axis is q1, Y-axis is q2, with no simplex constraint restriction.
    """
    p = np.array(p, dtype=float)
    
    if mode == 'IFS1':
        threshold_val = compute_ifs1_r2(p, t, n)
        title_str = f"Pure $\mathbb{{R}}^2$ IFS1 Boundary\nPeak p={p}, t={t}, n={n}"
    elif mode == 'IFS2':
        threshold_val = compute_ifs2_r2(p, t, n)
        title_str = f"Pure $\mathbb{{R}}^2$ IFS2 Boundary\nPeak p={p}, t={t}, n={n}"
    else:
        raise ValueError("mode must be 'IFS1' or 'IFS2'")
        
    # Generate an unconstrained bounding box grid around the peak
    margin = 1.5
    x_min, x_max = p[0] - margin, p[0] + margin
    y_min, y_max = p[1] - margin, p[1] + margin
    
    q1_vals = np.linspace(x_min, x_max, resolution)
    q2_vals = np.linspace(y_min, y_max, resolution)
    Q1, Q2 = np.meshgrid(q1_vals, q2_vals)
    
    utilities = np.zeros(Q1.shape)
    for i in range(resolution):
        for j in range(resolution):
            q_vector = np.array([Q1[i, j], Q2[i, j]])
            utilities[i, j] = compute_utility_r2(p, q_vector, t)
            
    fig, ax = plt.subplots(figsize=(7, 6))
    
    # Trace the unconstrained boundary contour
    ax.contour(Q1, Q2, utilities, levels=[threshold_val], 
               colors=['red'], linestyles='--', linewidths=2.5, zorder=4)
    
    # Plot the peak dot
    ax.scatter([p[0]], [p[1]], color='blue', s=120, zorder=5, label=f'Peak $p$ ({p[0]}, {p[1]})')
    
    ax.set_xlabel('$q_1$', fontsize=12)
    ax.set_ylabel('$q_2$', fontsize=12)
    ax.set_title(title_str, fontsize=12, fontweight='bold')
    ax.grid(True, linestyle=':', alpha=0.6)
    ax.legend(loc='upper right')
    
    plt.tight_layout()
    return fig, ax

# --- Main Demonstration Program ---
if __name__ == "__main__":
    # Test with a point completely outside a simplex layout (e.g., in the negative/positive quadrant)
    r2_peak = [0.8, -0.5]
    n_agents = 3
    t_val = 2  # Standard Euclidean distance metric circle profiles
    
    print(f"Plotting pure R^2 boundaries for peak={r2_peak}...")
    
    # Plot IFS1 in pure R^2
    plot_ifs_boundary_pure_r2(p=r2_peak, n=n_agents, t=t_val, mode='IFS1')
    plt.savefig("plots/pure_r2_ifs1.png", dpi=300)
    print("Saved 'pure_r2_ifs1.png'")
    
    # Plot IFS2 in pure R^2
    plot_ifs_boundary_pure_r2(p=r2_peak, n=n_agents, t=t_val, mode='IFS2')
    plt.savefig("plots/pure_r2_ifs2.png", dpi=300)
    print("Saved 'pure_r2_ifs2.png'")
    
    plt.show()