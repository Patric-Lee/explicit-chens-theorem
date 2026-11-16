import PlattPointSubsetKernel
import PlattPointPackets.S4B000221
import PlattPointPackets.S4B000222
import PlattPointPackets.S4B000223
import PlattPointPackets.S4B000224
import PlattPointPackets.S4B000225
import PlattPointPackets.S4B000226
import PlattPointPackets.S4B000227
import PlattPointPackets.S4B000228
import PlattPointPackets.S4B000229
import PlattPointPackets.S4B000230
import PlattGlobalGrid.S8B000027
namespace ChenEffective.PlattWindow.PointCovers.S8B000027
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000221.points ++ ChenEffective.PlattWindow.PointPackets.S4B000222.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000223.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000224.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000225.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000226.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000227.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000228.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000229.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000230.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000027.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000027.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000027
