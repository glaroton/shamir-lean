# Installing Lean and running this project

This guide takes you from a computer with nothing installed to checking the proofs and exploring them in an editor. It takes about 15 minutes, most of it downloads.

You need about **10 GB of free disk space** (Lean itself is about 3 GB, and Mathlib's precompiled files about 7 GB) and an internet connection.

## 1. Install Git

Git downloads the project.

- **Windows:** install [Git for Windows](https://git-scm.com/download/win) with the default options.
- **macOS:** open the Terminal app and run `git --version`. If Git is missing, macOS offers to install it; accept.
- **Linux:** use your package manager, for example `sudo apt install git` on Ubuntu or Debian.

## 2. Install elan (Lean's version manager)

`elan` installs Lean, and later picks the exact Lean version each project asks for (this one's is in the file `lean-toolchain`). You never install Lean directly.

- **Windows:** open PowerShell and run:

  ```powershell
  curl -O --location https://elan.lean-lang.org/elan-init.ps1
  powershell -ExecutionPolicy Bypass -f elan-init.ps1
  del elan-init.ps1
  ```

- **macOS and Linux:** open a terminal and run:

  ```bash
  curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
  ```

Accept the default answers. Then **close the terminal and open a new one**, so that it finds the new commands, and check:

```bash
elan --version
```

It should print a version number. If it says the command is not found, see [Troubleshooting](#troubleshooting).

## 3. Download the project

In the terminal, go to the folder where you want the project (for example `cd Documents`) and run:

```bash
git clone https://github.com/glaroton/shamir-lean.git
cd shamir-lean
```

All the following commands run inside this `shamir-lean` folder.

## 4. Download Mathlib, precompiled

```bash
lake exe cache get
```

`lake` is Lean's build tool; it came with elan. The first time, this command:

1. installs the Lean version the project needs (a few hundred MB),
2. downloads Mathlib's source,
3. downloads Mathlib's **precompiled** files, so that your computer does not have to compile Mathlib itself, which would take an hour or more.

It takes a few minutes and ends with a line like `Completed successfully` (or `Decompressed … file(s)`).

## 5. Check the proofs

```bash
lake build
```

This checks every proof in the project. It should take under a minute and end with:

```
Build completed successfully
```

If any proof were wrong, Lean would print an `error:` with the file and line instead.

To see which axioms the theorems rely on:

```bash
lake env lean CheckAxioms.lean
```

Each line should read `depends on axioms: [propext, Classical.choice, Quot.sound]`: the three standard axioms of Lean's logic, and nothing else.

## 6. Explore the proofs in an editor

Reading the files is fine, but Lean is meant to be used interactively: the editor shows, at each point of a proof, what is known and what is left to prove.

1. Install [Visual Studio Code](https://code.visualstudio.com/).
2. In VS Code, open the Extensions panel (the squares icon on the left), search for **Lean 4** and install it (publisher: leanprover).
3. Use **File → Open Folder…** and choose the `shamir-lean` folder. Open the whole folder, not a single file: otherwise the editor does not find Mathlib.
4. Open `Shamir/Example.lean`. The first time, it takes a minute to load Mathlib; a progress bar appears in the editor's margin.
5. A panel called **Lean Infoview** opens on the right. Put the cursor inside a proof, for example right after `by`, and the Infoview shows the goal at that point: the hypotheses above the line `⊢`, and what remains to prove after it. Move the cursor from tactic to tactic to watch the goal change.

Things to try:

- Hover over a name such as `Lagrange.interpolate` or `PMF.uniformOfFintype` to see its definition and documentation.
- Right-click a name and choose **Go to Definition** to jump into Mathlib.
- Break a proof on purpose, for example change the `5` in `share_at_1` to `4`. The editor underlines the error in red. Undo it afterwards.
- Below the last line of a file, type `#check Shamir.reconstruct` to see a theorem's statement in the Infoview.

Suggested reading order: `Shamir/Example.lean`, then `Shamir/Basic.lean` from the top. The [README](README.md) explains each statement in words.

## Troubleshooting

**`elan` or `lake`: command not found.** The terminal was opened before the installation. Close it and open a new one. If that does not help, add elan's folder to your PATH: `%USERPROFILE%\.elan\bin` on Windows, `~/.elan/bin` on macOS and Linux.

**`lake exe cache get` fails or downloads nothing.** Check your internet connection and run it again; it resumes where it stopped. Run it from inside the `shamir-lean` folder. If it keeps failing, `lake build` still works, but compiles Mathlib from scratch, which takes an hour or more.

**`lake build` starts compiling thousands of Mathlib files.** The precompiled files did not download. Stop it with Ctrl+C and run `lake exe cache get` again.

**VS Code shows errors on every `import Mathlib`.** You probably opened a single file instead of the folder; use **File → Open Folder…**. If you ran `lake exe cache get` while VS Code was open, run the command **Lean 4: Restart Server** (Ctrl+Shift+P, then type it).

**The Infoview does not appear.** Run the command **Lean 4: Infoview: Display Goal** (Ctrl+Shift+P, then type it).

## Learning more

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/): the standard tutorial for mathematicians, with exercises.
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4): a gentle start in the browser, nothing to install.
- [Lean community Zulip](https://leanprover.zulipchat.com/): the forum where Lean and Mathlib users ask questions; beginners are welcome.
