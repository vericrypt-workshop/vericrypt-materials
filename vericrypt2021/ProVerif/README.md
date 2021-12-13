# ProVerif


## Run from Docker

* Build a docker image from the Dockerfile using `docker build .`
* Use `docker image ls` to find the image's ID
* Create an empty directory `$DIR`: `mkdir $DIR`. We will use this directory to share data between the docker container and the host.
* Use `docker run -it -v $DIR:/data $IMAGE_ID` to launch a container from this image. Allow sharing directory `$DIR` when docker asks for permission.
  This will give you a shell inside the container.
  Use `exit` or Ctrl+D to close the shell.
* Use `docker ps -a` to find the container's ID
* Use `docker start -i $CONTAINER_ID` to get a shell again in this
  same container.

See https://github.com/FStarLang/FStar/wiki/Running-F%2A-from-a-docker-image
for more guidance on Docker.

### Connectivity Problems from inside Docker

- [Check DNS settings](https://docs.docker.com/engine/install/linux-postinstall/#specify-dns-servers-for-docker)

### Color Problems inside Docker

When you run applications such as emacs inside the terminal in which
you run Docker, colors are controled by the terminal, not by
Docker. Depending on the configuration of the terminal, some colors
may not be very visible.  Possible solutions:

* Run emacs in a new window, by enabling X support. See
https://github.com/FStarLang/FStar/wiki/Running-F%2A-from-a-docker-image
* Use a different terminal. For instance, on Windows, use the command-line instead of Powershell. Depending on your configuration, colors may be different.
* Adjust colors manually. For instance, on Windows, right-click the title bar of the Docker window; in the menu that opens, choose "Properties", then the "Colors" tab. You see the 16 colors represented by 16 squares on a line. First take note of the currently selected color, the one with a black border around the square (the others have a white border); it corresponds to the selected background color. To adjust a color, click on it and modify the red, green, blue quantities. When you are done, click again on the color that was selected at the beginning to restore the background color.

## Install manually

* On Mac OS X, you need to install XCode if you do not already have it. It can be downloaded from [https://developer.apple.com/xcode/](https://developer.apple.com/xcode/).
* Install ocaml, graphviz, and m4 using the package manager of your operating system.
* Either install from source
    * Download and unpack the source and documentation packages from [https://proverif.inria.fr](https://proverif.inria.fr).
    * Then, execute the `./build` script in unpacked the ProVerif directory. It might give you an error in file `display_interact` in the end; ignore it (it happens when building a graphical simulator that we are not going to use).
* Or on Windows, install from binary
    * Download and unpack the binary and documentation packages from [https://proverif.inria.fr](https://proverif.inria.fr).

### Editor support

* For Emacs, put the following into your `.emacs`, and replace `${PROVERIF}`
  by the directory to which you extracted the ProVerif archive:
```
(add-to-list 'load-path "${PROVERIF}/emacs")

(setq auto-mode-alist
	      (cons '("\\.horn$" . proverif-horn-mode) 
	      (cons '("\\.horntype$" . proverif-horntype-mode) 
	      (cons '("\\.pv[l]?$" . proverif-pv-mode) 
              (cons '("\\.pi$" . proverif-pi-mode) auto-mode-alist)))))
(autoload 'proverif-pv-mode "proverif" "Major mode for editing ProVerif code." t)
(autoload 'proverif-pi-mode "proverif" "Major mode for editing ProVerif code." t)
(autoload 'proverif-horn-mode "proverif" "Major mode for editing ProVerif code." t)
(autoload 'proverif-horntype-mode "proverif" "Major mode for editing ProVerif code." t)

```

## Testing the installation

For example, run `./proverif examples/pitype/secr-auth/DenningSacco-corr.pv`
in the ProVerif directory. 
