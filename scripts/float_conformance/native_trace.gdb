# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the LICENSE file in the root directory of this source tree.
set pagination off
set confirm off
set debuginfod enabled off
set auto-load off
set startup-with-shell off
set breakpoint pending on
python
import gdb, json
role = 'oracle' if int(gdb.parse_and_eval('$trace_oracle')) else 'model'
names = (['oracle_pair', 'mpfr_init2', 'mpfr_add', 'mpfr_mul', 'hw_add', 'hw_mul']
         if role == 'oracle' else
         ['l_Float_Model_ofBits', 'l_Float_Model_add', 'l_Float_Model_mul',
          'l_Float_Model_UnpackedFloat_add', 'l_Float_Model_UnpackedFloat_mul',
          'l_Float_Model_UnpackedFloat_roundWithAccuracy'])
if int(gdb.parse_and_eval('$trace_missing')):
    names[0] = '__float_missing_breakpoint__'
counts, callers, frames, exits = {}, {}, {}, []
class Count(gdb.Breakpoint):
    def __init__(self, name):
        self.label = name
        counts[name], callers[name] = 0, {}
        super().__init__(name)
    def stop(self):
        name = self.label
        counts[name] += 1
        older = gdb.newest_frame().older()
        caller = older.name() if older else '<none>'
        callers[name][caller] = callers[name].get(caller, 0) + 1
        if name not in frames:
            stack, frame = [], gdb.newest_frame()
            while frame and len(stack) < 8:
                stack.append(frame.name())
                frame = frame.older()
            frames[name] = stack
            print('FIRST_CALL ' + name)
            gdb.execute('bt 8')
            gdb.execute('x/8i $pc')
        return False
breakpoints = [Count(name) for name in names]
gdb.events.exited.connect(lambda event: exits.append(getattr(event, 'exit_code', None)))
end
run
python
result = dict(role=role, counts=counts, callers=callers, first_frames=frames, exits=exits)
print('FLOAT_TRACE ' + json.dumps(result, sort_keys=True))
ok = exits == [0] and all(counts[name] > 0 for name in names)
gdb.execute('quit ' + ('0' if ok else '1'))
end
