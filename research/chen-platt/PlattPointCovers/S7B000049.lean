import PlattPointSubsetKernel
import PlattPointPackets.S2B000225
import PlattPointPackets.S2B000226
import PlattPointPackets.S2B000227
import PlattPointPackets.S2B000228
import PlattPointPackets.S2B000229
import PlattPointPackets.S2B000230
import PlattGlobalGrid.S7B000049
namespace ChenEffective.PlattWindow.PointCovers.S7B000049
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000225.points ++ ChenEffective.PlattWindow.PointPackets.S2B000226.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000227.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000228.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000229.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000230.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000049.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000049.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000049
