import numpy as np
import matplotlib.pyplot as plt
import matplotlib.tri as tri
from matplotlib.animation import FuncAnimation
from matplotlib.lines import Line2D
from compute_ifs import compute_ifs1, compute_ifs2, compute_utility
from grid import peak_to_cartesian, generate_simplex_grid

def animate_ifs_boundary(p, n, mode, t_values, filename="ifs_animation.gif", resolution=150, fps=5):
    """
    Creates an animated GIF showing how the boundary of the satisfying region 
    changes dynamically as the utility parameter t varies.
    """
    p = np.array(p, dtype=float)
    q_points = generate_simplex_grid(resolution)
    
    # Project simplex coordinates to 2D
    xy_grid = np.array([peak_to_cartesian(q) for q in q_points])
    x, y = xy_grid[:, 0], xy_grid[:, 1]
    x_peak, y_peak = peak_to_cartesian(p)
    
    triangulation = tri.Triangulation(x, y)
    
    fig, ax = plt.subplots(figsize=(7, 6))

    def update(frame_idx):
        t = t_values[frame_idx]
        
        # 1. Clear the entire axes to cleanly wipe out old contours
        ax.clear()
        
        # 2. Redraw static background elements
        ax.plot([0, 1, 0.5, 0], [0, 0, np.sqrt(3)/2, 0], 'k-', lw=1.5)
        ax.scatter([x_peak], [y_peak], color='blue', s=120, zorder=5)
        
        # Static Vertex Labels
        ax.text(-0.05, -0.05, 'Alt 1\n(1, 0, 0)', fontsize=10, ha='center', va='top')
        ax.text(1.05, -0.05, 'Alt 2\n(0, 1, 0)', fontsize=10, ha='center', va='top')
        ax.text(0.5, np.sqrt(3)/2 + 0.03, 'Alt 3\n(0, 0, 1)', fontsize=10, ha='center', va='bottom')
        
        # 3. Compute thresholds and utilities for current t
        if mode == 'IFS1':
            threshold_val = compute_ifs1(p, t, n)
        elif mode == 'IFS2':
            threshold_val = compute_ifs2(p, t, n)
        else:
            raise ValueError("mode must be 'IFS1' or 'IFS2'")
            
        utilities = np.array([compute_utility(p, q, t) for q in q_points])
        
        # 4. Draw the new boundary contour line
        ax.tricontour(triangulation, utilities, levels=[threshold_val], 
                     colors=['red'], linestyles='--', linewidths=2.5, zorder=4)
        
        # 5. Reset plot view limits, titles, and legends for the cleared frame
        ax.set_xlim(-0.1, 1.1)
        ax.set_ylim(-0.1, 1.0)
        ax.axis('off')
        
        ax.set_title(f"Dynamic {mode} Boundary Evolution\nPeak={list(p)}, n={n} | Current t = {t:.2f}", 
                     fontsize=11, fontweight='bold')
        
        boundary_line = Line2D([0], [0], color='red', linestyle='--', lw=2, 
                               label=f'{mode} Bound (u(q) = {threshold_val:.3f})')
        peak_marker = Line2D([0], [0], marker='o', color='blue', linestyle='None', 
                             markersize=8, label=f'Agent Peak p')
        ax.legend(handles=[peak_marker, boundary_line], loc='upper right')
        
        return ax.collections

    # Create the animation object
    anim = FuncAnimation(fig, update, frames=len(t_values), interval=1000 // fps, blit=False)
    
    # Save the animation using Pillow
    print(f"Compiling animation frames into {filename}... Please wait.")
    anim.save(filename, writer='pillow', fps=fps)
    print(f"Successfully saved animation to {filename}")
    plt.close(fig)

# --- Main Demonstration Program ---
if __name__ == "__main__":
    my_peak = [0, 0, 1]
    n_agents = 2
    
    # Fine resolution sequence capturing the "inward then outward" shift
    t_sequence = np.concatenate([
        np.linspace(1.0, 3.0, num=20),       # Fast transition steps
        np.linspace(3.0, 22.0, num=20)        # Slow expansion/flattening steps
    ])
    
    # # 1. Animate IFS1 Boundary
    # animate_ifs_boundary(p=my_peak, n=n_agents, mode='IFS1', t_values=t_sequence, 
    #                      filename="plots/ifs1_breathing_boundary.gif", fps=4)
                         
    # 2. Animate IFS2 Boundary                     
    animate_ifs_boundary(p=my_peak, n=n_agents, mode='IFS2', t_values=t_sequence, 
                         filename="plots/ifs2_breathing_boundary.gif", fps=4)
    
