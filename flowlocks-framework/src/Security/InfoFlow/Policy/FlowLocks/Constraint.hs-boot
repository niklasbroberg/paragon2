module Security.InfoFlow.Policy.FlowLocks.Constraint where

import Security.InfoFlow.Policy.FlowLocks.GlobalPolicy
import Security.InfoFlow.Policy.FlowLocks.Lock
import Security.InfoFlow.Policy.FlowLocks.Policy


data Constraint mvar var name actset aid
    = LRT (GlobalPolicy name actset) 
          [Lock name aid] 
          (MetaPolicy mvar var name actset) 
          (MetaPolicy mvar var name actset)



