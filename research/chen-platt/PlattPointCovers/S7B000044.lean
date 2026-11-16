import PlattPointSubsetKernel
import PlattPointPackets.S2B000204
import PlattPointPackets.S2B000205
import PlattPointPackets.S2B000206
import PlattPointPackets.S2B000207
import PlattPointPackets.S2B000208
import PlattGlobalGrid.S7B000044
namespace ChenEffective.PlattWindow.PointCovers.S7B000044
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000204.points ++ ChenEffective.PlattWindow.PointPackets.S2B000205.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000206.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000207.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000208.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000044.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000044.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000044
