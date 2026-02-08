import which from 'which';

export function whichSyncImpl(command, options) {
  options = options || {};

  return which.sync(command, {
    nothrow: true,
    path: options.path,
    pathExt: options.pathExt,
  });
}

export function whichAllSyncImpl(command, options) {
  options = options || {};

  return which.sync(command, {
    nothrow: true,
    all: true,
    path: options.path,
    pathExt: options.pathExt,
  });
}
