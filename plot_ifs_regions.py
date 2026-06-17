import numpy as np
import matplotlib.pyplot as plt
import matplotlib.tri as tri
from matplotlib.lines import Line2D
from compute_ifs import compute_ifs1, compute_ifs2, compute_utility

def peak_to_cartesian(p):
    """Transforms a 3D simplex coordinate into 2D Cartesian coordinates."""
    p = np.array(p)
    x = p[1] + 0.5 * p[2]
    y = p[2] * np.sqrt(3) / 2.0
    return x, y

def generate_simplex_grid(resolution=100):
    """Generates a dense grid of valid outcome distributions q over the 3-simplex."""
    grid = []
    for i in range(resolution + 1):
        for j in range(resolution + 1 - i):
            k = resolution - i - j
            grid.append([i / resolution, j / resolution, k / resolution])
    return np.array(grid)

def plot_ifs_region(p, n, t, mode='IFS1', resolution=120):
    """
    Plots the simplex highlighting the specific region where outcome distributions q 
    satisfy the agent's IFS condition (u(q) >= IFS_value), along with a dot at peak p.
    """
    p = np.array(p, dtype=float)
    
    # 1. Compute the threshold value for the given peak
    if mode == 'IFS1':
        threshold_val = compute_ifs1(p, t, n)
        title_str = f"Outcome Distributions Satisfying IFS1\nPeak p={p}, t={t}, n={n}"
    elif mode == 'IFS2':
        threshold_val = compute_ifs2(p, t, n)
        title_str = f"Outcome Distributions Satisfying IFS2\nPeak p={p}, t={t}, n={n}"
    else:
        raise ValueError("mode must be 'IFS1' or 'IFS2'")
        
    # 2. Generate outcome distribution grid points and evaluate their utilities
    q_points = generate_simplex_grid(resolution)
    utilities = np.array([compute_utility(p, q, t) for q in q_points])
    
    # Binary indicator: 1 if satisfies IFS, 0 otherwise
    satisfies_ifs = (utilities >= threshold_val).astype(float)
    
    # 3. Project coordinates to 2D
    xy_grid = np.array([peak_to_cartesian(q) for q in q_points])
    x, y = xy_grid[:, 0], xy_grid[:, 1]
    x_peak, y_peak = peak_to_cartesian(p)
    
    # 4. Plotting
    fig, ax = plt.subplots(figsize=(7, 6))
    triangulation = tri.Triangulation(x, y)
    
    # Highlight the region satisfying the threshold using a distinct colored layer
    # Levels [0.5, 1.5] isolates the satisfied zone (value == 1.0)
    ax.tricontourf(triangulation, satisfies_ifs, levels=[0.5, 1.5], colors=['#FF9999'], alpha=0.7)
    
    # Draw boundary lines of the simplex
    ax.plot([0, 1, 0.5, 0], [0, 0, np.sqrt(3)/2, 0], 'k-', lw=1.5)
    
    # Plot the agent's peak position
    ax.scatter([x_peak], [y_peak], color='blue', s=120, zorder=5, label=f"Peak p {list(p)}")
    
    # Vertex Labels
    ax.text(-0.05, -0.05, 'Alt 1\n(1, 0, 0)', fontsize=10, ha='center', va='top')
    ax.text(1.05, -0.05, 'Alt 2\n(0, 1, 0)', fontsize=10, ha='center', va='top')
    ax.text(0.5, np.sqrt(3)/2 + 0.03, 'Alt 3\n(0, 0, 1)', fontsize=10, ha='center', va='bottom')
    
    # Final styling
    ax.set_title(title_str, fontsize=11, fontweight='bold')
    ax.set_xlim(-0.1, 1.1)
    ax.set_ylim(-0.1, 1.0)
    ax.axis('off')
    
    # Dummy handle for the highlighted region label in legend
    import matplotlib.patches as mpatches
    region_patch = mpatches.Patch(color='#FF9999', alpha=0.7, label=f'Satisfies {mode} (u(q) $\geq$ {threshold_val:.3f})')
    ax.legend(handles=[ax.collections[0] if not ax.collections else region_patch, region_patch], loc='upper right')
    
    plt.tight_layout()
    return fig, ax

def plot_ifs_boundary(p, n, t, mode='IFS1', resolution=150):
    """
    Plots the simplex with a dashed line exactly at the boundary where 
    u(q) == IFS_value, without filling the interior.
    """
    p = np.array(p, dtype=float)
    
    if mode == 'IFS1':
        threshold_val = compute_ifs1(p, t, n)
        title_str = f"Boundary of IFS1 Satisfying Region\nPeak p={p}, t={t}, n={n}"
    elif mode == 'IFS2':
        threshold_val = compute_ifs2(p, t, n)
        title_str = f"Boundary of IFS2 Satisfying Region\nPeak p={p}, t={t}, n={n}"
    else:
        raise ValueError("mode must be 'IFS1' or 'IFS2'")
        
    q_points = generate_simplex_grid(resolution)
    utilities = np.array([compute_utility(p, q, t) for q in q_points])
    
    xy_grid = np.array([peak_to_cartesian(q) for q in q_points])
    x, y = xy_grid[:, 0], xy_grid[:, 1]
    x_peak, y_peak = peak_to_cartesian(p)
    
    fig, ax = plt.subplots(figsize=(7, 6))
    triangulation = tri.Triangulation(x, y)
    
    # Trace the boundary using tricontour at the exact threshold value
    contour = ax.tricontour(triangulation, utilities, levels=[threshold_val], 
                             colors=['red'], linestyles='--', linewidths=2.0, zorder=4)
    
    # Draw boundary lines of the simplex
    ax.plot([0, 1, 0.5, 0], [0, 0, np.sqrt(3)/2, 0], 'k-', lw=1.5)
    ax.scatter([x_peak], [y_peak], color='blue', s=120, zorder=5, label=f"Peak p {list(p)}")
    
    # Vertex Labels
    ax.text(-0.05, -0.05, 'Alt 1\n(1, 0, 0)', fontsize=10, ha='center', va='top')
    ax.text(1.05, -0.05, 'Alt 2\n(0, 1, 0)', fontsize=10, ha='center', va='top')
    ax.text(0.5, np.sqrt(3)/2 + 0.03, 'Alt 3\n(0, 0, 1)', fontsize=10, ha='center', va='bottom')
    
    # Legend setup
    from matplotlib.lines import Line2D
    boundary_line = Line2D([0], [0], color='red', linestyle='--', lw=2, 
                           label=f'{mode} Boundary (u(q) = {threshold_val:.3f})')
    ax.legend(handles=[boundary_line], loc='upper right')
    
    ax.set_title(title_str, fontsize=11, fontweight='bold')
    ax.set_xlim(-0.1, 1.1)
    ax.set_ylim(-0.1, 1.0)
    ax.axis('off')
    plt.tight_layout()
    return fig, ax


def plot_multi_t_boundaries(p, n, t_list, mode='IFS1', resolution=180):
    """
    Plots the simplex with boundaries of the satisfying regions for multiple t values.
    Each boundary is plotted in a different color with a corresponding legend entries.
    """
    p = np.array(p, dtype=float)
    q_points = generate_simplex_grid(resolution)
    
    xy_grid = np.array([peak_to_cartesian(q) for q in q_points])
    x, y = xy_grid[:, 0], xy_grid[:, 1]
    x_peak, y_peak = peak_to_cartesian(p)
    
    fig, ax = plt.subplots(figsize=(8, 7))
    triangulation = tri.Triangulation(x, y)
    
    # Color palette for different t values
    colors = [
        '#E6194B',  # Red
        '#3CB44B',  # Green
        '#0082C8',  # Blue
        '#F58231',  # Orange
        '#911EB4',  # Purple
        '#46F0F0',  # Cyan/Teal
        '#F032E6',  # Magenta/Pink
        '#7F7F7F'   # Dark Gray
    ]
    legend_elements = []
    
    # Pre-calculate utilities for each unique t to avoid redundant loops
    for idx, t in enumerate(t_list):
        color = colors[idx % len(colors)]
        
        # 1. Compute threshold value
        if mode == 'IFS1':
            threshold_val = compute_ifs1(p, t, n)
        elif mode == 'IFS2':
            threshold_val = compute_ifs2(p, t, n)
        else:
            raise ValueError("mode must be 'IFS1' or 'IFS2'")
            
        # 2. Compute individual utilities under parameter t
        utilities = np.array([compute_utility(p, q, t) for q in q_points])
        
        # 3. Draw boundary curve
        ax.tricontour(triangulation, utilities, levels=[threshold_val], 
                     colors=[color], linestyles='--', linewidths=2.0, zorder=4)
        
        # Add to custom legend
        legend_elements.append(Line2D([0], [0], color=color, linestyle='--', lw=2,
                                      label=f't = {t} (Bound: {threshold_val:.3f})'))

    # Draw boundary lines of the simplex
    ax.plot([0, 1, 0.5, 0], [0, 0, np.sqrt(3)/2, 0], 'k-', lw=1.5)
    
    # Plot agent's peak
    ax.scatter([x_peak], [y_peak], color='black', s=140, marker='X', zorder=5, 
               label=f"Peak p {list(p)}")
    legend_elements.insert(0, Line2D([0], [0], marker='X', color='black', linestyle='None',
                                      markersize=10, label=f"Agent Peak p {list(p)}"))

    # Add vertex text labels
    ax.text(-0.05, -0.05, 'Alt 1\n(1, 0, 0)', fontsize=10, ha='center', va='top')
    ax.text(1.05, -0.05, 'Alt 2\n(0, 1, 0)', fontsize=10, ha='center', va='top')
    ax.text(0.5, np.sqrt(3)/2 + 0.03, 'Alt 3\n(0, 0, 1)', fontsize=10, ha='center', va='bottom')
    
    title_str = f"Comparison of {mode} Boundaries for Multiple $t$ Values\n(n = {n} Agents)"
    ax.set_title(title_str, fontsize=12, fontweight='bold')
    ax.legend(handles=legend_elements, loc='upper right', fontsize=9)
    ax.set_xlim(-0.1, 1.1)
    ax.set_ylim(-0.1, 1.0)
    ax.axis('off')
    plt.tight_layout()
    return fig, ax


# Helper Wrappers
def plot_ifs1_region(p, n, t): return plot_ifs_region(p, n, t, mode='IFS1')
def plot_ifs2_region(p, n, t): return plot_ifs_region(p, n, t, mode='IFS2')
def plot_ifs1_boundary(p, n, t): return plot_ifs_boundary(p, n, t, mode='IFS1')
def plot_ifs2_boundary(p, n, t): return plot_ifs_boundary(p, n, t, mode='IFS2')


# --- Main Demonstration Program ---
if __name__ == "__main__":
    # Define an asymmetric test peak, 3 agents, and an ell_1 utility function
    test_peak = [0.2, 0.3, 0.5]
    n_agents = 3
    t_parameter = 1  # l_1 metric (linear cost)
    
    print(f"Plotting satisfying outcome regions for peak={test_peak}...")
    
    # # 1. Plot and save IFS1 satisfying zone
    # plot_ifs1_region(p=test_peak, n=n_agents, t=t_parameter)
    # plt.savefig(f"plots/satisfied_region_t{t_parameter}_n{n_agents}_ifs1.png", dpi=300)
    
    # # 2. Plot and save IFS2 satisfying zone
    # plot_ifs2_region(p=test_peak, n=n_agents, t=t_parameter)
    # plt.savefig(f"plots/satisfied_region_t{t_parameter}_n{n_agents}_ifs2.png", dpi=300)
    
    # # 3. Plot and save IFS1 satisfying boundary
    # plot_ifs1_boundary(p=test_peak, n=n_agents, t=t_parameter)
    # plt.savefig(f"plots/satisfied_boundary_t{t_parameter}_n{n_agents}_ifs1.png", dpi=300)
    
    # # 4. Plot and save IFS2 satisfying boundary
    # plot_ifs2_boundary(p=test_peak, n=n_agents, t=t_parameter)
    # plt.savefig(f"plots/satisfied_boundary_t{t_parameter}_n{n_agents}_ifs2.png", dpi=300)
        
    # # 5. Plot and save IFS1 satisfying multi-t boundaries
    # plot_multi_t_boundaries(p=test_peak, n=n_agents, t_list=[1,2,3,4,8,16,32], mode="IFS1")
    # plt.savefig(f"plots/satisfied_boundary_t1248_n{n_agents}_ifs1.png", dpi=300)
        
    # 6. Plot and save IFS2 satisfying multi-t boundaries
    plot_multi_t_boundaries(p=test_peak, n=n_agents, t_list=[1,1.5,2,3,8,12,32], mode="IFS2")
    plt.savefig(f"plots/satisfied_boundary_t1248_n{n_agents}_ifs2.png", dpi=300)

    plt.show()