import PlattPointSubsetKernel
import PlattPointPackets.S1B000274
import PlattPointPackets.S1B000275
import PlattPointPackets.S1B000276
import PlattPointPackets.S1B000277
import PlattGlobalGrid.S5B000104
namespace ChenEffective.PlattWindow.PointCovers.S5B000104
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000274.points ++ ChenEffective.PlattWindow.PointPackets.S1B000275.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000276.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000277.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000104.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000104.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000104
