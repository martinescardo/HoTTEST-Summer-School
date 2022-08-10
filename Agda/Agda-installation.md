# Instructions on how to get Agda 2.6.2.2

## Online

Thanks to Amélia Liao, there's an [online version](https://hcomp.io/) available,
which means you won't have to install anything.  But if you would like to
install Agda locally, please see below.

## Mac

If you're a Mac user who already uses homebrew, the process is painless: just
run `brew install` agda and get ready to wait a while.

If you're a Mac user who doesn't already use homebrew, follow the [instructions
here](https://brew.sh/) to get it working.

## Linux

If you're an Arch or Fedora user, then `pacman -S agda` or `yum install agda`
should work. See also [theses Arch instructions](https://pastebin.com/jj2c2dqR).

If you're Debian/Ubuntu, then you should install Agda through `cabal`, because
the Agda in the repositories of the operating system is outdated. See [these
instructions](https://agda.readthedocs.io/en/v2.6.2.2/getting-started/installation.html).

## Windows

For Windows, see [these instructions](https://pastebin.com/Zguv4743). (Thanks
Todd Waugh Ambridge!)

## Editing Agda code

Most people use emacs with agda-mode to edit, but you can also use neovim with
cornelis or vscode with the agda-mode port.

To get emacs with agda-mode set up, there's a [tutorial
here](https://agda.readthedocs.io/en/v2.6.2.2/getting-started/installation.html#running-the-agda-mode-program)

To get neovim with corenlis setup, there's installation instructions on [their
GitHub](https://github.com/isovector/cornelis)

To get the vscode plugin setup, see
[here](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode)

## Agda in Markdown files

If you're using emacs, then add the following at the very end of your `.emacs`
file (in your home directory)

```
(add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))
```

to enable agda-mode for Markdown files with Agda code, like the lecture notes
and exercises.

## Checking that everything works

After installing Agda, you should check that it's installed correctly by
type-checking the [Hello, Agda!
program](https://agda.readthedocs.io/en/v2.6.2.2/getting-started/hello-world.html#hello-agda)

## Working outside the repository

If you would like to work on the exercises and have the lecture notes available
outside (for `open import`) the repository, then you should register the
repository as a library:

In `~/.agda/libraries` add the line
```
~/HoTTEST-Summer-School/Agda/agda-lectures.agda-lib
```
and then add the line `agda-lectures` to `~/.agda/defaults`.

## Getting help

If you're having trouble installing Agda, please ask for help in the
`#agda-installation` channel on the summer school's Discord server.
