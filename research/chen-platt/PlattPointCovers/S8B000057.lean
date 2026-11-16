import PlattPointSubsetKernel
import PlattPointPackets.S5B000225
import PlattPointPackets.S5B000226
import PlattPointPackets.S5B000227
import PlattPointPackets.S5B000228
import PlattPointPackets.S5B000229
import PlattPointPackets.S5B000230
import PlattPointPackets.S5B000231
import PlattPointPackets.S5B000232
import PlattPointPackets.S5B000233
import PlattPointPackets.S5B000234
import PlattPointPackets.S5B000235
import PlattPointPackets.S5B000236
import PlattPointPackets.S5B000237
import PlattGlobalGrid.S8B000057
namespace ChenEffective.PlattWindow.PointCovers.S8B000057
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000225.points ++ ChenEffective.PlattWindow.PointPackets.S5B000226.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000227.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000228.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000229.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000230.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000231.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000232.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000233.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000234.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000235.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000236.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000237.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000057.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000057.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000057
