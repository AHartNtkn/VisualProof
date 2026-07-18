import { validateProductionInterfaceAssets } from './production-interface-assets'

const errors = validateProductionInterfaceAssets(process.cwd())
for (const error of errors) console.error(error)
if (errors.length > 0) process.exitCode = 1
