
import * as cp from "child_process"

const inherit = { stdio: ['inherit', 'inherit', 'inherit']}
const pipe = { stdio: ['pipe', 'pipe', 'pipe']}

export function anyCommand(command, opts) {
  if(opts.forwardOutput) {
    cp.execSync(command, inherit)
  } else {
    cp.execSync(command, pipe) 
  }
}
