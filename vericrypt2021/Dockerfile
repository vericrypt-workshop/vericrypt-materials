FROM ubuntu:20.04

ENV TZ=Asia/Kolkata
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN apt update

RUN apt install -y sudo

# Create user
RUN useradd -ms /bin/bash vericrypt
RUN echo "vericrypt ALL=(ALL:ALL) NOPASSWD:ALL" >> /etc/sudoers
USER vericrypt
WORKDIR /home/vericrypt

# Some commonly used tools
RUN sudo apt install -y software-properties-common
RUN sudo apt -qq update

RUN sudo apt install -y wget
RUN sudo apt -qq update

# EverParse release, comes with F*, Kremlin too
RUN wget https://github.com/project-everest/everparse/releases/download/v2021.12.10/everparse_v2021.12.10_Linux_x86_64.tar.gz

RUN tar -xvzf everparse_v2021.12.10_Linux_x86_64.tar.gz

RUN rm everparse_v2021.12.10_Linux_x86_64.tar.gz

# Set up F* environment

ENV FSTAR_HOME="/home/vericrypt/everparse"
ENV KREMLIN_HOME="/home/vericrypt/everparse"
ENV QD_HOME="/home/vericrypt/everparse"
ENV PATH="/home/vericrypt/everparse/bin:${PATH}"
ENV LD_LIBRARY_PATH="/home/vericrypt/everparse/bin:${LD_LIBRARY_PATH}"

# emacs editor and F* plugin

RUN sudo apt install -y emacs libglu1-mesa xfonts-terminus fonts-symbola

ENV LANG C.UTF-8
RUN emacs --batch \
	--eval "(require 'package)" \
	--eval "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" \
	--eval "(package-initialize)" \
	--eval "(package-refresh-contents)" \
	--eval "(package-install 'fstar-mode)" \
	--eval "(package-install 'flycheck)"

COPY --chown=vericrypt:vericrypt .emacs /home/vericrypt/.emacs

# DY*

RUN wget -O dystar.tar.gz https://github.com/REPROSEC/dolev-yao-star/archive/refs/tags/vericrypt21.tar.gz

RUN tar -xvzf dystar.tar.gz

RUN mv dolev-yao-star-vericrypt21 dystar

RUN rm dystar.tar.gz

ENV DY_HOME="/home/vericrypt/dystar"

RUN sudo apt install make

# For ProVerif

RUN sudo apt install -y opam ocaml graphviz libgtk2.0-dev libexpat1-dev m4
RUN opam init --disable-sandboxing -y
ENV OPAM_SWITCH_PREFIX='/home/vericrypt/.opam/default'
ENV CAML_LD_LIBRARY_PATH='/home/vericrypt/.opam/default/lib/stublibs:/usr/local/lib/ocaml/4.08.1/stublibs:/usr/lib/ocaml/stublibs'
ENV OCAML_TOPLEVEL_PATH='/home/vericrypt/.opam/default/lib/toplevel'
ENV PKG_CONFIG_PATH='/home/vericrypt/.opam/default/lib/pkgconfig'
ENV MANPATH="${MANPATH}:/home/vericrypt/.opam/default/man"
ENV PATH="/home/vericrypt/.opam/default/bin:${PATH}"
RUN opam install -y ocamlfind lablgtk
RUN wget https://proverif.inria.fr/proverif2.04.tar.gz
RUN wget https://proverif.inria.fr/proverifdoc2.04.tar.gz
RUN tar -xzf proverif2.04.tar.gz
RUN tar -xzf proverifdoc2.04.tar.gz
RUN mv proverif2.04 proverif
WORKDIR proverif
RUN ./build
ENV PATH="/home/vericrypt/proverif:${PATH}"
WORKDIR /home/vericrypt
RUN rm proverif2.04.tar.gz proverifdoc2.04.tar.gz

# VeriCrypt materials repo

RUN git clone https://github.com/vericrypt-workshop/vericrypt-materials.git
