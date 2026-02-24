# Game AI That Can't Cheat

A pathfinding algorithm for 2D game AI that guarantees honest behavior—no cheating.

## Overview

Game AI often "cheats" when given overly broad heuristics or goals. This repository provides a **verified pathfinding solution** that eliminates cheating by design:

- **Vision-based goals**: AI only pursues targets it can actually see
- **Collision-aware paths**: AI only traverses paths that respect game physics and obstacles
- **Guaranteed correctness**: Eliminates trial-and-error path validation
- **Improved efficiency**: Fewer wasted computation cycles on invalid paths

The result is both more believable AI and more reliable game behavior.

## Technical Details

### Grid-Based World
The algorithm operates on 2D grid worlds for simplicity and performance. The underlying concepts can be generalized to arbitrary polygons using similar verification techniques.

### Formal Verification
All algorithms are implemented and verified in **Dafny**, a language designed for formal program verification. This ensures mathematical correctness at compile-time.

### Engine Integration
Verified algorithms can be exported to **C#** or other languages for integration with game engines like **Unity**.

## Why This Matters

Traditional pathfinding often separates path generation from validation, leading to invalid states. This library unifies both processes for guaranteed correct paths on the first attempt.