/*
    Interval: Virtual register
    RegRecord: Physical register
    RefPosition: Points of def/use of virtual/physical registers
    
    NodeLocations: Each GenTree node are assigned pair of locations (using location += 2).
        1st location is all uses, internal registers and all but last ref.
        2nd location is for the final def (if any)
        
    regRecord->assignedInterval:
        Interval currently assigned to the register
    
    interval->assignedReg:
        Register to which this interval has been assigned at some point.
        If interval is active, this is the register it occupies.
        
    interval->physReg:
        Register to which an interval is currently assigned.
    
    spillCost:
        Maintains information on how expensive it is to spill the register
        at any given point.
*/
foreach (candidate_variable)
{
    // For all arg variables, set the fixed arg register in interval
    if (candidate_variable == isArg)
    {
        regRecord = physRegRecord[candidate_variable->argReg];
        interval = intervals[candidate_variable];
        
        interval->assignedReg = regRecord;
        regRecord->assignedInterval = interval;
    }
}

=============
// allocateRegister()

foreach (interval) {
    // If interval is for arg variable, make it active.
    if (interval->isArg) {
        interval->isActive = true;
    }
}

foreach (register) {
    // 1. Update `nextFixedRef` to point to the 1st refposition where
    //    register is used.
    // 2. Update `fixedRegs` to tracks all fixed registers used through
    //    out the method
    // 3. Update `nextIntervalRef` to track next usage (def/use) of
    //    interval assigned to register
    regRecord = physRegRecord[register];
    if (regRecord->firstRefPosition) {
        nextLocation = regRecord->firstRefPosition->nodeLocation;
        fixedRegs |= register;
    }
    else {
        nextLocation = MaxLocation
        fixedReg ~= register;
    }
    
    nextFixedRef[register] = nextLocation;
    
    interval = regRecord->assignedInterval;
    if (interval) {
        // only true for incoming arg registers
        nextIntervalRef[register] = interval->nextRefposition->nodeLocation;
    }
}

foreach (currentRefPosition: refpositions) {
    refType = currentRefPosition->refType;    
    if (currentRefPosition->nodeLocation > prevLocation) {
        // If there are registers to free, free them here
        freeRegisters(regsToFree);
    }
    prevLocation = currentRefPosition->nodeLocation;
    
    if ((refType == RefTypeBB) || (refType == RefTyepeDummyDef)) {
        // If there are registers to free, free them here
        freeRegisters(regsToFree);
        
        // Nothing more to do for block boundaries
        if (refType == RefTypeBB) continue;
    }
    
    if (refType == RefTypeKillGCRefs) {
        // Spill GC refs and nothing more to do.
        registers_assigned = currentRefPosition->registerAssignment;
        unassignPhysReg(registers_assigned: r);
        continue;
    }
    
    if (currentRefPosition->isPhysReg) {
        assignedInterval = currentRefPosition->register->assignedInterval;
        if (refType == RefTypeFixedReg) {
            // For fixed registers, if the assigned interval of the register
            // of a `currentRefPosition`interval is not active, then unassign
            // that interval from the register.
            if (!assignedInterval->isActive) {
                assignedInterval = nullptr;
                spillCost[register] = 0;
            }
            continue; // nothing more to do.
        }
        if (refType == RefTypeKill) {
            unassignPhysReg(assignedInterval, assignedInterval->recentRefPosition);
            continue; // nothing more to do.
        }
    }
    
    if (refType == RefTypeExpUse) {
        continue; // nothing more to do.
    }
    
    shouldAllocate = false;
    currentInterval = currentRefPosition->interval;
    assignedRegister = currentInterval->physReg;
    
    // For RefTypeParamDef and RefTypeZeroInit, decide if we should allocate
    // for `currentRefPosition`.
    if ((refType == RefTypeParamDef) || (refType == RefTypeZeroInit)) {
        if (conditions_met) {
            // No need to allocate if:
            // 1. Blocks have EH boundary because params will be on stack.
            // 2. If parameter is passed on stack or it is low ref-count parameter
            //       that is used (lastUse == false).
            // 3. If already on stack for BIT_CAST
            // 4. If the interval is write-thru && RefTypeZeroInit
            shouldAllocate = false;            
        }
    }
    
    if (currentInterval->isUpperVector && currentInterval->isPartiallySpilled) {
        // intervals are partially spilled if we generate save/restore refpositions for them
        // before a call.
        shouldAllocate = false;
    }
    
    if (!shouldAllocate) {
        if (assignedRegister == VALID) {
            unassignPhysReg(assignedRegister, currentRefPosition);
        }
        continue; // nothing more to do.
    }
    
    //TODO: special put arg
    
    if ((refType == RefTypeUse) && (assignedRegister != VALID)) {
        // If there is no assignedRegister, it means that register was previously
        // assigned (at previous uses or, if this is the first use, then at the "def"
        // but the register got re-assigned. In that case, we need to reload it.
        currentRefPosition->reload = true;
    }

    if (assignedRegister == VALID) {
        if (!currentInterval->isActive) {
            // If this is inactive interval and it already has a register assigned
            // and this is def, then activate the interval.
            if (refType == RefTypeDef) currentInterval->isActive = true;
        }
    }

    if ((assignedRegister == VALID) && (currentRefPosition == currentInterval->firstRefPosition)) {
        // If this refposition is the first refposition, and it already got a register assigned,
        // it means that it is a parameter. In such case, check if it covers the entire lifetime
        // of this variable.

        // Do this by checking if next location where this register is used is beyond the last
        // refposition of this interval. If `3` is the last refposition and next usage of
        // assignedRegister is at B, then we can safely assume that it covers the lifetime of
        // the variable.
        // ---1-------2------3-----
        // ---A-------------------B  <-- covers 1,2,3
        // vs.
        // ---1-------2------3-----
        // ---A----------B---------  <-- Doesn't cover entire 1,2,3
        nextLocationPhysRegUsed = nextFixedRef[assignedRegister];
        if (nextLocationPhysRegUsed <= currentInterval->lastInterval->nodeLocation) {
            // Doesn't cover the lifetime. Does it even cover upto the next refposition?
            if ((nextLocationPhysRegUsed <= nextRefPosition->nodeLocation) || (!matchesPreference)) {
                // Nope
                unassignPhysReg(assignedRegister); // do no spill though
                assignedRegister = INVALID;
            }
        }
    }

    if (assignedRegister == VALID)
    {
        if (assignedRegister->hasConflicts(currentRefPosition)) {
            // There is a conflict and we need to move register to new one
        }
        else if (assignedRegister == currentRefPosition->registerAssignment) {
            // This is the right one. Keep it
        }
        else
        {
            // It is assigned but not in the register we wanted
            if (refType == RefTypeDef) {
                // We want new register for this definition based on
                // currentRefPosition's preference.
                assignedRegister = INVALID;
            }
            else {
                // Allocate a different register 
                copyReg = assignCopyRef(currentRefPosition);

                // Track the registers to free

                continue; // nothing more to do
            }
        }
    }

    if (assignedRegister == INVALID)
    {
        if (currentRefPosition->RegOptional()) {
            // If it is optional to assign register, check few things and decide if
            // we should truely allocate or not:
            if (conditions_met) {
                // 1. lastUse requiring a reload
                // 2. isWriteThru and nextRefPosition is inside code block
                // 3. RefTypeUpperVectorRestore && value is on stack
                shouldAllocate = false;
            }
        }

        if (shouldAllocate) {
            assignedRegister = allocateReg(currentInterval, currentRefPosition);
        }

        if (assignedRegister == INVALID) {
            // We couldn't assign a register, mark the interval as spilled
            currentInterval->isSpilled = true;
        }
        else if (refType == RefTyepeDummyDef) {
                setInVarRegForBB(curBBNum, varNum, assignedRegister);
        }
    }

    if (assignedRegister == VALID) {
        // A register was allocated, either now or in the past, record it.
        currentRefPosition->registerAssignment = assignedRegister;
        currentInterval->physReg = assignedRegister;

        // See if we can unassign it immediately after this refPosition
        bool unassign = false;
        if (conditions_met)
        {
            // 1. isWriteThru interval and currentRefPosition is not the last use and currentRefPosition is spillAfter.
            // 2. currentRefposition is lastUse && nextRefPosition == nullptr, with an exception of RefTypeExpUse, in which
            //    case, we need to continue keep the register assigned.
            unassign = true;
        }

        if (unassign)
        {
            regsToFree |= assignedRegister;
        }
    }

    freeRegisters(regsToFree);
}

==========================================

// Unassign `register` and spill the interval at `spillRefPosition`.
unassignPhysReg(register, spillRefPosition)
{
    assignedInterval = register->assignedInterval;
    assert(assignedInterval == spillRefPosition->interval);
    
    makeRegisterAvailable(register);
    
    if ((assignedInterval->physReg != register) && (assignedInterval->physReg != VALID))
    {
        // If this `assignedInterval` is currently not in the "same" `register`, then
        // no need to do anything else.
    }
    
    // If `assignedInterval` is assigned to this `register`, then we need to
    // unassign it, but just remember that `register` was ever assigned to
    // the `assignedInterval`.
    assignedInterval->physReg = INVALID;
    assignedInterval->assignedReg = register;
    
    // Update register's assignedInterval to previousInterval, if any.
    register->assignedInterval = register->previousInterval;
    register->previousInterval = nullptr;
    
    // Also spill the `assignedInterval` if it is active and has more refpositions.
    if (assignedInterval->isActive && spillRefPosition->nextRefPosition)
    {
        if(!spillRefPosition->lastUse)
        {
            spillRefPosition->spillAfter = true;
        }
        assignedInterval->isActive = false;
        assignedInterval->isSpilled = true;
    }    
}

==========================================

