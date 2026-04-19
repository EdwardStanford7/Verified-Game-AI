#show link: underline
#show link: it => text(fill: blue, it)

= 2D Game AI That Doesn't Cheat

== Motivation

One of the most important aspects of games is enemy AI and ensuring it is fully correct. A common issue with AI pathfinding in games is making sure the AI doesn't go through walls or try to path towards something it isn't supposed to be able to see. The first issue could be solved with a full physics engine but that is expensive and doesn't solve the second problem. We propose a verified game AI written in Dafny that ensures the agent is behaving correctly.

== Prior Work

- Existing verified Dijkstra algorithm in Dafny that we can use as a reference for verified A\* \
  #link("https://github.com/YashvanGH/dafny-dijkstra")
- Existing visibility library and paper on various algorithms for computing visibility. More research required on whether we want to do visibility in the continuous plane and then discretize to a grid for A\*, or just start in the discrete world for visibility as well. \
  #link("https://www.fhnw.ch/plattformen/computervision/rd-projects/robotics/visibility") \
  #link("https://aircconline.com/csit/papers/vol10/csit101801.pdf")

== The Goal

A verified AI library initially written in Dafny but then exported to C\# for use in games.

== Approach

This project will be composed of two main algorithms, written and verified in Dafny. A 2D visibility problem will check what goals an agent can attempt to pathfind towards, and a verified A\* algorithm will give paths to those goals that are guaranteed to be the shortest and not clip through any existing geometry. This will be designed as a library that a game developer could use to facilitate their game AI. The user will pass a point, a set of polygons, and a value function to the library, which will internally run the verified visibility problem, run the verified A\* on all visible points, then return the path with the highest value according to the given value function.

== Timeline

By early March, we hope to have the two algorithms implemented and the structure of the library in place. We will also have the verification goals figured out and a set of unimplemented `ensures` on both algorithms. The second phase of the project will then be completing all the verification goals until all the `ensures` statements are satisfied. If we have time, a stretch goal would be to write a simple game in C\# (maybe Unity) that uses the exported version of our library to demonstrate its effectiveness.
