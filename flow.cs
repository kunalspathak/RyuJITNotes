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
foreach (interval)
{
    // If interval is for arg variable, make it active.
    if (interval->isArg)
    {
        interval->isActive = true;
    }
}

foreach (register)
{
    // 1. Update `nextFixedRef` to point to the 1st refposition where
    //    register is used.
    // 2. Update `fixedRegs` to tracks all fixed registers used through
    //    out the method
    // 3. Update `nextIntervalRef` to track next usage (def/use) of
    //    interval assigned to register
    regRecord = physRegRecord[register];
    if (regRecord->firstRefPosition)
    {
        nextLocation = regRecord->firstRefPosition->nodeLocation;
        fixedRegs |= register;
    }
    else
    {
        nextLocation = MaxLocation
        fixedReg ~= register;
    }
    
    nextFixedRef[register] = nextLocation;
    
    interval = regRecord->assignedInterval;
    if (interval)
    {
        // only true for incoming arg registers
        nextIntervalRef[register] = interval->nextRefposition->nodeLocation;
    }
}

foreach (currentRefPosition: refpositions)
{
    refType = currentRefPosition->refType;    
    if (currentRefPosition->nodeLocation > prevLocation)
    {
        // If there are registers to free, free them here
        freeRegisters(regsToFree);
    }
    prevLocation = currentRefPosition->nodeLocation;
    
    if ((refType == RefTypeBB) || (refType == RefTyepeDummyDef))
    {
        // If there are registers to free, free them here
        freeRegisters(regsToFree);
        
        // Nothing more to do for block boundaries
        if (refType == RefTypeBB) continue;
    }
    
    if (refType == RefTypeKillGCRefs)
    {
        // Spill GC refs and nothing more to do.
        registers_assigned = currentRefPosition->registerAssignment;
        unassignPhysReg(registers_assigned: r);
        continue;
    }
    
    if (currentRefPosition->isPhysReg)
    {
        assignedInterval = currentRefPosition->register->assignedInterval;
        if (refType == RefTypeFixedReg)
        {
            // For fixed registers, if the assigned interval of the register
            // of a `currentRefPosition`interval is not active, then unassign
            // that interval from the register.
            if (!assignedInterval->isActive)
            {
                assignedInterval = nullptr;
                spillCost[register] = 0;
            }
            continue; // nothing more to do.
        }
        if (refType == RefTypeKill)
        {
            unassignPhysReg(assignedInterval, assignedInterval->recentRefPosition);
            continue; // nothing more to do.
        }
    }
    
    if (refType == RefTypeExpUse)
    {
        continue; // nothing more to do.
    }
    
    shouldAllocate = false;
    currentInterval = currentRefPosition->interval;
    assignedRegister = currentInterval->physReg;
    
    // For RefTypeParamDef and RefTypeZeroInit, decide if we should allocate
    // for `currentRefPosition`.
    if ((refType == RefTypeParamDef) || (refType == RefTypeZeroInit))
    {
        if (conditions_met)
        {
            // No need to allocate if:
            // 1. Blocks have EH boundary because params will be on stack.
            // 2. If parameter is passed on stack or it is low ref-count parameter
            //       that is used (lastUse == false).
            // 3. If already on stack for BIT_CAST
            // 4. If the interval is write-thru && RefTypeZeroInit
            shouldAllocate = false;            
        }
    }
    
    // TODO: For upper vector save/restore too set `shouldAllocate`.
    
    if (!shouldAllocate)
    {
        if (assignedRegister == VALID)
        {
            unassignPhysReg(assignedRegister, currentRefPosition);
        }
        continue; // nothing more to do.
    }
    
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

