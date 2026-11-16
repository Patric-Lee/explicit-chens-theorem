import PlattPointSubsetKernel
import PlattPointPackets.S2B000103
import PlattPointPackets.S2B000104
import PlattPointPackets.S2B000105
import PlattPointPackets.S2B000106
import PlattGlobalGrid.S7B000017
namespace ChenEffective.PlattWindow.PointCovers.S7B000017
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000103.points ++ ChenEffective.PlattWindow.PointPackets.S2B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000105.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000106.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000017.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000017.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000017
