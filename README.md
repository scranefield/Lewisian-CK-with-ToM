# Lewisian-CK-with-ToM
This code implements the recognition of Lewisian common knowledge based on theory-of-mind reasoning

## Instructions

You can either use SWI Prolog via Docker or install SWI Prolog on your computer.

### Set-up
- To use Docker, run this command:

   ```
   docker run -it -v PATH:/user/docker/supplementary -w /user/docker/supplementary swipl:8.4.2
   ```

   where PATH is replaced by the path to your clone of this repository.

- To install SWI Prolog locally, see https://www.swi-prolog.org/download/stable. This code was developed and tested using SWI Prolog version 8.4.3 on Windows. There is no Docker image available for version 8.4.3, but 8.4.2 works.

### Instructions
If using Docker, the docker run command above will result in an SWI Prolog query prompt being displayed. If using a local installation of SWI Prolog:
1. Open a command or terminal window in the top level of this Demo Code folder (or, if using Docker, the docker run command above will result in 
2. Run SWI Prolog (the command is swipl on Windows, and probably also for other OSs; see above for how to use Docker).

Then open queries.txt in a text editor and copy each Prolog query (one at a time, without the initial "?- " and including the "." at the end), paste it after the Prolog "?-" prompt and press Enter.

### Notes
A subfolder of this Demo Code folder contains a clone of the original Pfc code at https://github.com/finin/pfc, with a minor modification to avoid operator clashes with SWI Prolog. 

WARNING: there is a later adaptation of Pfc that is available in SWI Prolog via an external 'pack' or via https://github.com/logicmoo/pfc. DO NOT USE THAT VERSION WITH THIS CODE. Its justification/2 predicate has a different meaning than the one in the original code, and also has a bug.
