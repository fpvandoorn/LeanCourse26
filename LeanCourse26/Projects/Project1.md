# Project 1: contribute a formal conjecture

In your first project, you will contribute to the Formal Conjectures project by creating a new Lean statement of a mathematical research conjecture. There is a list of formalised mathematical conjectures at https://google-deepmind.github.io/formal-conjectures/; your task is to formalise a conjecture which is not yet present in this list.

This should be a relatively small task, and should only require 10-50 lines of code.
You can do this project alone, or in pairs.

You are allowed to ask any AI questions, but it is not allowed to write the formalization for you.

### Detailed Instructions

1. Clone the Formal Conjectures repository: https://github.com/google-deepmind/formal-conjectures
  See [`Git.md`](./Git.md) for Git instructions.
2. Choose a conjecture to formalise, and enter it in [this table](https://uni-bonn.sciebo.de/s/LWckyNXFZoDzKTf) together with your name.

    Please make sure it is not contained in the Formal Conjectures repository already.
    If the conjecture you want to formalise is already "taken" by a fellow student, please choose another one.
    Here are some sources for a new conjectures. (You are free to choose a different research conjecture.)
    - Wikipedia: https://en.wikipedia.org/wiki/List_of_conjectures, https://en.wikipedia.org/wiki/Category:Conjectures or elsewhere
    - Choose one from the Formal Conjectures issue list: https://github.com/google-deepmind/formal-conjectures/issues?q=is%3Aissue+is%3Aopen+no%3Aassignee+-linked%3Apr+label%3A%22new+conjecture%22
    - Another list of conjectures, like https https://oeis.org/ (search for "conjecture"); [Optimization constants](https://github.com/teorth/optimizationproblems) or [Kourovka](https://arxiv.org/abs/1401.0300)


3. Read the Formal Conjectures [contribution guidelines](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md), especially the sections "Contribution process", "File structure conventions", "The @[category] attribute" and and "Style Guidelines".

    The Formal Conjectures repository requires contributors to sign the contributor agreement (see their Contribution page), which requires a Google account.
    Please sign this agreement. Alternatively, you can write a comment when creating your pull request stating that you accept the contribution guidelines.
4. Create a branch for your conjecture.
5. Formalise your conjecture in Lean, following the guidelines from Formal Conjectures. You are not allowed to generate this with generative AI tools.
    Hint: look at other entries in the repository and mimic those.
    - Write a documentation string with an English statement, enclosed by `/-- -/`.
    - You can also add a variant of the statement.
6. **If the previous step was short** (< 10 lines of Lean code, counting only definitions and theorem statements), **formalize a second one**. Create a separate branch/pull request for the second conjecture.
7. **Ask another student or a tutor to check whether your formalization looks correct**.
8. Commit and push your changes to your own fork of the repository. Then make a pull request with your formal conjecture to the [upstream repository](https://github.com/google-deepmind/formal-conjectures).
9. Add a link to your pull request(s) to [the table](https://uni-bonn.sciebo.de/s/LWckyNXFZoDzKTf).
10. After you receive comments on your pull request, incorporate them, and push them to your branch.
11. Repeat step 10 until the pull request is merged.

### Deadlines

* November 18: Create a first version of your conjecture and make a pull request.
* November 27: Incorporate all requested changes from the first review on your pull request.
* December 4 (not strict): Repeatedly incorporate requests by a reviewer until your pull request is merged.
