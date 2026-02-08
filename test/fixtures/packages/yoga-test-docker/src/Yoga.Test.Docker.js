import { spawnSync } from "child_process";
import path from "path";
import { fileURLToPath } from "url";

// Get the directory where tests are running from
// We need to go up from yoga-test-docker/output/.../Yoga.Test.Docker/ to the test directory
const getComposeDir = () => {
  // When called from a test, process.cwd() should be the workspace root
  return process.cwd();
};

export const dockerComposeUp = (composeFile) => () => {
  const cwd = getComposeDir();
  console.log(`🐳 Starting test service (${composeFile})...`);
  
  const result = spawnSync(
    "docker",
    ["compose", "-f", composeFile, "up", "-d"],
    { cwd, stdio: "pipe" }
  );
  
  if (result.error || result.status !== 0) {
    const errorMsg = result.error 
      ? result.error.message 
      : result.stderr.toString();
    throw new Error(`Failed to start Docker: ${errorMsg}`);
  }
  
  return (onError, onSuccess) => {
    onSuccess();
  };
};

export const dockerComposeDown = (composeFile) => () => {
  const cwd = getComposeDir();
  console.log(`\n🛑 Stopping test service (${composeFile})...`);
  
  const result = spawnSync(
    "docker",
    ["compose", "-f", composeFile, "down"],
    { cwd, stdio: "pipe" }
  );
  
  if (result.error || result.status !== 0) {
    console.error("Warning: Failed to stop Docker:", result.error || result.stderr.toString());
  }
  
  return (onError, onSuccess) => {
    onSuccess();
  };
};

export const isServiceHealthy = (composeFile) => () => {
  const cwd = getComposeDir();
  
  const result = spawnSync(
    "docker",
    ["compose", "-f", composeFile, "ps", "--format", "json"],
    { cwd, stdio: "pipe" }
  );
  
  if (result.error || result.status !== 0) {
    return (onError, onSuccess) => onSuccess(false);
  }
  
  const output = result.stdout.toString();
  const healthy = output.includes('"Health":"healthy"');
  
  return (onError, onSuccess) => {
    onSuccess(healthy);
  };
};
