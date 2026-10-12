#!/bin/sh
# Pass-through stand-in for landrun on a kernel without Landlock (this VM). Drops landrun's sandbox flags and runs
# the command directly. Only for checking our own trusted proof; it provides no isolation.
while [ $# -gt 0 ]; do
  case "$1" in
    --) shift; break ;;
    --rw|--rwx|--ro|--rox|--env) shift 2 ;;
    *) shift ;;
  esac
done
exec "$@"
