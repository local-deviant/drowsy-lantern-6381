# Sokoban solver

Room-decomposed push-optimal A* solver: each room is solved on its own with an assignment heuristic, dead-square and frozen 2x2 pruning, then the rooms' walks are joined into one LURD move string.
