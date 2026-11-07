"""Checked refutations of ordinary input packets; NOT accepted H69 dispositions.
Only an explicit owner/human decision can change their status. No original
statement, definition or premise is edited by this registry.
"""
PENDING={
 "Solidity.Theory.Mutability.ContractWorld.World.enter_static":{
   "module":"PayableWitnesses","helper":"payable_static_inputs_impossible",
   "question":"Q-STATIC-VALUE",
   "reason":"Frozen Context.Mode ordinary implies isStatic=false; readOnly implies value=0. Static=true AND value!=0 is impossible.",
   "status":"ordinary-joint-witness-blocked-pending-disposition"}}
