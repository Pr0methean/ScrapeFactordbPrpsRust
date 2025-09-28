FROM ubuntu:latest
RUN apt-get install libecm-dev
RUN rustup toolchain install nightly
RUN cargo +nightly build --release
RUN mkfifo composites