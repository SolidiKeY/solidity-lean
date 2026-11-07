#!/usr/bin/env python3
"""Exercise frozen text guard against proof, statement and definition changes."""
from check_frozen import frozen_view

original = '''@[irreducible] def f (n : Nat) := n + 1
theorem t (n : Nat) : (if { checked := false }.checked then n else n) = n := by
  rfl
private def outcome : Nat → Option Nat
  | 0 => none
  | n => some n
'''
proof = original.replace('  rfl\n', '  exact rfl\n')
statement = original.replace('then n else n', 'then n else 0')
definition = original.replace('n + 1', 'n + 2')
equations = original.replace('| 0 => none', '| 0 => some 0')
assert frozen_view(original) == frozen_view(proof), 'proof-only edit rejected'
for altered in (statement, definition, equations):
    assert frozen_view(original) != frozen_view(altered), 'frozen change missed'
print('frozen text guard: proof edit accepted; statement and definition changes rejected')

for altered in ("import Evil.Module\n" + original,
                "namespace Fraud\n" + original,
                original + "axiom injected : False\n",
                original + "set_option maxHeartbeats 9999999\n",
                original + "local notation example => 0\n",
                original + "universe u\n", original + "variable (x : Nat)\n",
                original + "include h\n", original + "section Test\n"):
    assert frozen_view(original) != frozen_view(altered), "command change missed"
print("frozen text guard: import, namespace, axiom and option changes rejected")
position_a = 'theorem a : True := by\n  trivial\ninclude h\ntheorem b : True := by\n  trivial\n'
position_b = 'theorem a : True := by\n  trivial\ntheorem b : True := by\n  trivial\ninclude h\n'
assert frozen_view(position_a) != frozen_view(position_b), 'command relocation missed'
print('frozen text guard: command relocation rejected')

for shortcut in ("sorry", "sorryAx", "admit", "native_decide", "ofReduceBool", "unsafe", "run_tac", "axiom"):
    changed = original.replace("  rfl\n", "  " + shortcut + "\n", 1)
    assert frozen_view(original) != frozen_view(changed), shortcut
print("frozen text guard: new raw trust-shortcut indicators rejected")
# The raw scan is deliberately conservative: comments and strings can flag too.
assert frozen_view(original) != frozen_view(original + '-- sorry\n'), 'comment indicator missed'
assert frozen_view(original) != frozen_view(original.replace('  rfl\n', '  exact "native_decide"\n', 1)), 'string indicator missed'
assert frozen_view(original) == frozen_view(original.replace('  rfl\n', '  exact sorryThing\n', 1)), 'identifier substring flagged'
print('frozen text guard: raw-scan false-positive boundary and identifier boundary checked')
assert frozen_view(original) != frozen_view(original.replace('  rfl\n', "  exact sorry'\n", 1)), 'apostrophe false-positive boundary changed'
comment_token = original.replace('  rfl\n', '  -- sorry\n  rfl\n', 1)
relocated_token = original.replace('  rfl\n', '  -- note\n  sorry\n', 1)
assert frozen_view(comment_token) == frozen_view(relocated_token), 'raw count limitation changed'
print('frozen text guard: apostrophe false-positive and equal-count limitation documented')
