import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
df = pd.read_csv('gttt4x4.txt')
plt.figure(figsize=(10, 8))
#plt.axhline(y=0, color='r', linestyle='-')
#plt.plot(df['iteration'], df['pn-dn'], label='pn-dn')
#plt.xlabel('Iteration')
#plt.ylabel('pn - dn')
orange_patch = mpatches.Patch(color='red', label='pn-dn')
red_patch = mpatches.Patch(color='blue', label='Terminal')
# Create some mock data
#t = np.arange(0.01, 10.0, 0.01)
#data1 = np.exp(t)
#data2 = np.sin(2 * np.pi * t)

fig, ax1 = plt.subplots()
#ax1.set_title('R = 0.1',weight = 'bold')
color = 'red'
ax1.set_xlabel('Iterations', weight = 'bold')
ax1.set_ylabel('pn-dn', color=color, weight = 'bold')
ax1.plot(df['iteration'], df['pn-dn'], color=color)
ax1.tick_params(axis='y', labelcolor=color)

ax2 = ax1.twinx()  # instantiate a second axes that shares the same x-axis

color = 'blue'
ax2.set_ylabel('Terminal Nodes', color=color, weight = 'bold')  # we already handled the x-label with ax1
ax1.set_xlim(0, 11000)
ax2.set_ylim(0, 5000)
#ax1.set_ylim(0, 130)
ax2.plot(df['iteration'], df['node'], color=color)
ax2.tick_params(axis='y', labelcolor=color)
plt.legend(handles=[red_patch, orange_patch])
fig.tight_layout()  # otherwise the right y-label is slightly clipped
import tikzplotlib
#plt.savefig('block1.0.png')
tikzplotlib.save("gttt4x4track.tex")