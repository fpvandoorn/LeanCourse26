## Project 2: your own formalisation project

## Personal Info

Please fill out the following. Fill in the project topic once you have decided.
```
First & last name student 1:
First & last name student 2 (optional):
Project topic:
```

## Project Description

During the second half of the course you will work on a project in any area of mathematics of your choice.

**You should put your project files in this folder, and push to a fork.**
You are also allowed to create a new repository.

We recommend that you work on your project in groups of two.
`Git.md` has a section `Working with a partner` about handling this in git.

## Formalization Topics

You can choose a topic in any area of mathematics.

A good topic should be:
* not yet in mathlib (although it's also fine to give a different proof of something already in mathlib);
* not too hard (don't overestimate how much you can do in your project);
* not require too many prerequisites that are not yet part of mathlib. If it does require many prerequisites, doing one/some of these prerequisites can be your project instead.

On the mathlib website there are some useful pages:
* [topics in mathlib](https://leanprover-community.github.io/mathlib-overview.html)
* [undergraduate topics in mathlib](https://leanprover-community.github.io/undergrad.html)
* [the full contents of mathlib](https://leanprover-community.github.io/mathlib4_docs/) (use the search in the top right)

Some suggested topics are listed [here](./Topics.md).

## Formalization Tips

Here are some tips for your project.

### Read relevant mathlib files

* There is a rough Mathlib overview here: https://leanprover-community.github.io/mathlib-overview.html
  This can give you an idea what is already in Mathlib.
* Make sure you look through Mathlib what related concepts to your project already exists. It is useful to use https://leansearch.net/ for this
* Look at the related work in more detail in the Mathlib docs:
  https://leanprover-community.github.io/mathlib4_docs/.
  For some results, opening the file in Lean will give you even more information.
* The link above is for the newest version of Mathlib. It is possible that some things have changed slightly since the course started. There is also a version of the documentation pages for the exact version of Mathlib this course uses, here: https://florisvandoorn.com/LeanCourse25/docs/
* Step through some of the proofs in Lean.
  You can open the file locally by going to e.g.
  `LeanCourse25/.lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean`
  Note that the `.lake` folder is hidden in VSCode sidebar, but you can navigate through it with `ctrl+O` or `cmd+O`.

### Searching

During class we already discussed searching using the name (using autocomplete or the mathlib docs), the statement (using `#click_suggestions`, `exact?`, `apply?`, `have?`, `rw?`), using natural language (leansearch) or precise syntax (loogle).

### Asking for help

* If you have trouble with anything, make sure to ask the tutor or teacher for help during class, the tutorial or the Lean hacking session.
* If you are stuck on something, try replacing it by `sorry` and move on to the next part until you can ask about it.
* You are allowed to ask any AI questions, but it is not allowed to write part of the formalization for you. If you're using AI for your project, you need to document how you used it.

### Writing definitions

It is useful to find a definition that already exists in mathlib and is similar to what you want.
Then you can mimic the structure of that definition.
This can also be useful in deciding whether to use `def`, `structure` or `class`.

## Project Presentation

You are *required* to give a presentation about the project during your exercise class. This should be a short presentation (approx. 15-20 minutes) describing the mathematical topic and the formalization. For the formalization, there are multiple things you can describe:
* Are there definitions that were tricky to write in Lean? Did you revise the way you defined something, and did that make it easier?
* Was there a proof that was harder to formalize than expected?
* Which tactics were particularly useful?
* ...

## Deadlines

* November 18: Choose a project topic and enter it in [this table](https://uni-bonn.sciebo.de/s/LWckyNXFZoDzKTf) (second sheet). Ask your tutor (or a lecturer) to approve your project topic.

* Projects are due on January 18, so that we can announce exam admittance by January 20.

## Handing in your project

To "hand in" your project, you just have to push to your fork of GitHub, and check that all the files show up on GitHub.

* Your project should contain a short description of its contents, entered in [`Description.md`](./Description.md) (or a pdf file uploaded here).

* If you used slides/notes for your presentation, please also include them.
