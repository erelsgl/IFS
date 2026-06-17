import numpy as np
import matplotlib.pyplot as plt
import matplotlib.tri as tri
from compute_ifs import compute_ifs1, compute_ifs2

def peak_to_cartesian(p):
    """
    Transforms a 3D simplex coordinate (p1, p2, p3) where sum(p) = 1
    into 2D Cartesian coordinates (x, y) for an equilateral triangle.
    The vertices of the triangle are:
    A (Alternative 1): (0, 0)
    B (Alternative 2): (1, 0)
    C (Alternative 3): (0.5, sqrt(3)/2)
    """
    p = np.array(p)
    x = p[1] + 0.5 * p[2]
    y = p[2] * np.sqrt(3) / 2.0
    return x, y

def generate_simplex_grid(resolution=50):
    """Generates valid probability distributions over a 3-simplex."""
    peaks = []
    for i in range(resolution + 1):
        for j in range(resolution + 1 - i):
            k = resolution - i - j
            p1 = i / resolution
            p2 = j / resolution
            p3 = k / resolution
            peaks.append([p1, p2, p3])
    return np.array(peaks)

def plot_ifs_contour(t, n, mode='IFS1', resolution=60):
    """
    Computes and plots the contours of IFS1 or IFS2 over the 3-simplex.
    """
    peaks = generate_simplex_grid(resolution)
    
    # Compute the IFS values for each point in the grid
    if mode == 'IFS1':
        values = [compute_ifs1(p, t, n) for p in peaks]
        title_str = f"IFS1 (Maximin) Contours\n(t = {t}, n = {n})"
    elif mode == 'IFS2':
        values = [compute_ifs2(p, t, n) for p in peaks]
        title_str = f"IFS2 (Minimax) Contours\n(t = {t}, n = {n})"
    else:
        raise ValueError("mode must be either 'IFS1' or 'IFS2'")
        
    # Project 3D peaks into 2D Cartesian coordinates
    xy = np.array([peak_to_cartesian(p) for p in peaks])
    x = xy[:, 0]
    y = xy[:, 1]
    z = np.array(values)

    # Setup the plot
    fig, ax = plt.subplots(figsize=(7, 6))
    
    # Create the triangulation for nonuniform/structured simplex grids
    triangulation = tri.Triangulation(x, y)
    
    # Refined mask to prevent plotting outside the valid triangle boundaries
    # (handles edge precision issues)
    # Draw contour lines and filled contours
    contour_filled = ax.tricontourf(triangulation, z, levels=15, cmap='viridis')
    contour_lines = ax.tricontour(triangulation, z, levels=15, colors='k', linewidths=0.5)
    
    ax.clabel(contour_lines, inline=True, fontsize=8, fmt='%.2f')
    fig.colorbar(contour_filled, ax=ax, label='Utility Value')

    # Draw and label the boundary triangle edges
    ax.plot([0, 1, 0.5, 0], [0, 0, np.sqrt(3)/2, 0], 'k-', lw=1.5)
    ax.text(-0.05, -0.05, 'Alt 1\n(1, 0, 0)', fontsize=10, ha='center', va='top')
    ax.text(1.05, -0.05, 'Alt 2\n(0, 1, 0)', fontsize=10, ha='center', va='top')
    ax.text(0.5, np.sqrt(3)/2 + 0.03, 'Alt 3\n(0, 0, 1)', fontsize=10, ha='center', va='bottom')

    ax.set_title(title_str, fontsize=12, fontweight='bold')
    ax.set_xlim(-0.1, 1.1)
    ax.set_ylim(-0.1, 1.0)
    ax.axis('off')
    plt.tight_layout()
    
    return fig, ax

if __name__ == "__main__":
    # Parameters for illustration
    t_val = 1     # Ell_2 utility (Euclidean)
    n_agents = 3  # 3 agents sharing the budget
    res = 50      # Resolution of the simplex grid
    
    print(f"Generating IFS1 and IFS2 contour plots for t={t_val}, n={n_agents}...")
    
    # Generate IFS1 Plot
    plot_ifs_contour(t=t_val, n=n_agents, mode='IFS1', resolution=res)
    plt.savefig(f"plots/ifs1_contour_t{t_val}_n{n_agents}.png", dpi=300)
    print("Saved 'ifs1_contour_t2_n3.png'")
    
    # Generate IFS2 Plot
    plot_ifs_contour(t=t_val, n=n_agents, mode='IFS2', resolution=res)
    plt.savefig(f"plots/ifs2_contour_t{t_val}_n{n_agents}.png", dpi=300)
    print("Saved 'ifs2_contour_t2_n3.png'")
    
    # Display the plots on screen
    plt.show()
