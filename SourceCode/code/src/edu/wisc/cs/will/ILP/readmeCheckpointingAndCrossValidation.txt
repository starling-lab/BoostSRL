
Notes from Trevor Walker (4/2/09) on Checkpointing and Cross-Validation
-----------------------------------------------------------------------

Single ILP Run Checkpointing
----------------------------

A single run of ILP (via the ILPouterLoop) can now check point after each repetition of the LearnOneClause inner loop.   If something bad occurs, the checkpoint will allow the run to be restarted at the point of the last checkpoint.

By default, I left checkpoint off.  For development purposes, you probably don't want it to be on.  Once we are in a production environment, this should probably default to true.  To enable checkpointing, you can use ILPouterLoop.setCheckpoingEnabled().  Or, if you use ILPouterLoop as your main (which actually points to a separate edu.wisc.cs.will.ILP.ILPMain now), you can specify "-checkpoint" to enable it. 

Checkpoints are stored in the working directory.  If you are having trouble with something, you might want to check to see if they are there and messing you up.  Obviously, they shouldn't be created if you have checkpointing turned off.

Caveat:  If you are using checkpoint, your run dies after checkpointing, and you then change the parameters of the run, bad things will probably happen.  Basic checks are performed to make sure the checkpoint belongs to the same run.  However, most of the parameter settings found in the LearnOneClause inner loop are not cached and not checked.  After resuming with different parameters, the new parameters will be used, but some of the old answers may still exist.  When in doubt, remove the checkpoint files.


Cross Validation
----------------

Cross-validation is now supported by WILL. 

You can use cross-validation by creating a ILPouterLoop, then passing that outerLoop to a new ILPCrossValidationLoop object.  Then you can do the cross-validation by calling ILPCrossValidationLoop.executeCrossValidation().  Alternatively, if you are using ILPouterLoop as your main, you can just specify the number of folds to run at the end of the normal command line.

It is always safe to call executeCrossValidation() with a cross validation loop, instead of using the ILPouterLoop.executeOuterLoop().  If the number of folds is set to 1, executeCrossValidation() calls ILPouterLoop.executeOuterLoop() without any extra overhead.

If the number of folds is greater than 1, the cross validation loop will partition the positive and negative examples and then execute the outer loop for each fold with the appropriate examples.

It is possible to split the work of a cross-validation run across multiple processors or machines.  Each processor/machine can be assigned one or more folds to work on. 

The instances that is assigned fold 0 will setup the initial state and will collate the results after all of the fold have finished.  If you are using ILPouterLoop as your main, there is now a -fold option to specify the fold to work on.  That parameter will only result in the indicated fold being processed.  If you need a single process to work on multiple folds, there isn't a command-line option right now, but you can use the appropriate ILPCrossValidationLoop constructor to specify it.

As folds are finished, there results are written to disk in the working directory.  If a process fails to complete its folds, it can be restarted and only the unfinished folds will be run.

Caveat:  Do not assign multiple processors or machine to fold 0.  It will probably work, but two or more of the processes might do the example permutation and splitting, which would be bad.  If this becomes a problem, I can probably get a locking mechanism in place, but it will be a bit of a hack.

Caveat:  There is no way to disable saving the cross-validation state and finished folds to disk.  These file are how the separate processes communicate.  If this is a problem (say, because BL doesn't allow us disk access), I can relax this constraint.  However, we will be limited to running all folds in a single process.

Caveat:  Since files are saved to disk, the caveat concerning parameter changes from above apply to cross-validation also.  If you change parameters for a run, make sure you clean up the cross-validation state and fold result files.  Otherwise, some of the results will most likely be from previous parameter settings.


SVN

I committed all of this code to subversion.  I am in sync with the most recent repository copy, so you shouldn't have too much trouble updating.  However, if you do, let me know and I can help resolve the problem.  There were some pretty major changes in this commit, so you will probably want to update as soon as possible so you don't get too out of sync.

I tried to make this as transparent as possible.  Hopefully, you won't even notice the changes.  However, if you notice WILL acting weird or failing when it didn't previously, let me know and I will figure out what happened.



