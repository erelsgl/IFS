import os
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from matplotlib.lines import Line2D

def animate_distance_contour_pure_r2(filename="lt_distance_r2_evolution.gif", resolution=250, fps=5):
    """
    Animates a contour line through all points P in pure R^2 where 
    distance_t(A, P) == distance_t(A, B), with t ranging from 1 to 20.
    """
    # Ensure the output directory exists
    os.makedirs("plots", exist_ok=True)
    
    # 1. Define points A and B in R^2
    A = np.array([0.0, 1.0])
    B = np.array([0.5, 0.5])
    
    # 2. Define a bounding box grid around the center point A
    margin = 1.2
    x_min, x_max = A[0] - margin, A[0] + margin
    y_min, y_max = A[1] - margin, A[1] + margin
    
    x_vals = np.linspace(x_min, x_max, resolution)
    y_vals = np.linspace(y_min, y_max, resolution)
    X, Y = np.meshgrid(x_vals, y_vals)
    
    fig, ax = plt.subplots(figsize=(7, 6))
    
    # Define smoothly transitioning t-values from 1 up to 20
    t_values = np.concatenate([
        np.linspace(1.0, 5.0, num=17),
        np.linspace(6.0, 20.0, num=15)
    ])

    def update(frame_idx):
        t = t_values[frame_idx]
        ax.clear()
        
        # Plot points A and B
        ax.scatter([A[0]], [A[1]], color='blue', s=130, marker='o', zorder=5, label='Point A (0, 1)')
        ax.scatter([B[0]], [B[1]], color='darkorange', s=130, marker='s', zorder=5, label='Point B (0, 0.5)')
        
        # Calculate target distance threshold ||A - B||_t
        target_dist = (np.sum(np.abs(A - B) ** t)) ** (1.0 / t)
        
        # Vectorized calculation of distance ||A - P||_t across the mesh grid
        grid_distances = (np.abs(X - A[0])**t + np.abs(Y - A[1])**t) ** (1.0 / t)
            
        # Draw the unconstrained boundary contour line where distance equals the target
        ax.contour(X, Y, grid_distances, levels=[target_dist], 
                   colors=['red'], linestyles='--', linewidths=2.5, zorder=4)
        
        # Figure properties adjustments
        ax.set_xlim(x_min, x_max)
        ax.set_ylim(y_min, y_max)
        ax.set_xlabel('$q_1$', fontsize=12)
        ax.set_ylabel('$q_2$', fontsize=12)
        ax.grid(True, linestyle=':', alpha=0.6)
        
        ax.set_title(f"Points $P$ where $\ell_t(A, P) = \ell_t(A, B)$ in $\mathbb{{R}}^2$\nCurrent $t$ = {t:.2f}", 
                     fontsize=11, fontweight='bold')
        
        # Custom Legend handles
        contour_line = Line2D([0], [0], color='red', linestyle='--', lw=2.5, label='Equidistant Line')
        ax.legend(loc='upper right', fontsize=9)
        
        return ax.collections

    # Create and compile animation
    anim = FuncAnimation(fig, update, frames=len(t_values), interval=250, blit=False)
    output_path = os.path.join("plots", filename)
    
    print(f"Compiling R^2 equidistant line animation into {output_path}... Please wait.")
    anim.save(output_path, writer='pillow', fps=4)
    print(f"Animation successfully written to {output_path}")
    plt.close(fig)

if __name__ == "__main__":
    # Run the visualization sequence
    animate_distance_contour_pure_r2(filename="lt_distance_r2_evolution.gif")