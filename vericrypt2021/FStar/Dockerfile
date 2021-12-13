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

RUN sudo apt install -y software-properties-common
RUN sudo apt -qq update

RUN sudo apt install -y wget
RUN sudo apt -qq update

RUN wget https://github.com/project-everest/everparse/releases/download/v2021.12.10/everparse_v2021.12.10_Linux_x86_64.tar.gz

RUN tar -xvzf everparse_v2021.12.10_Linux_x86_64.tar.gz

ENV FSTAR_HOME="/home/vericrypt/everparse"
ENV KREMLIN_HOME="/home/vericrypt/everparse"
ENV QD_HOME="/home/vericrypt/everparse"
ENV PATH="/home/vericrypt/everparse/bin:${PATH}"
ENV LD_LIBRARY_PATH="/home/vericrypt/everparse/bin:${LD_LIBRARY_PATH}"


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

RUN wget https://github.com/REPROSEC/dolev-yao-star/archive/refs/heads/vericrypt.zip

RUN unzip dolev-yao-star-vericrypt.zip

ENV DY_HOME="/home/vericrypt/dolev-yao-star-vericrypt"
