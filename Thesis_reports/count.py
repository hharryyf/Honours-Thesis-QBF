import pandas as pd
import matplotlib.pyplot as plt
df = pd.read_csv('plot_statistic.csv')
plt.scatter(df['visit_ratio'], df['Solve_more'])
plt.show()