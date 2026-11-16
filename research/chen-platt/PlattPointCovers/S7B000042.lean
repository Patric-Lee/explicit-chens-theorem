import PlattPointSubsetKernel
import PlattPointPackets.S2B000196
import PlattPointPackets.S2B000197
import PlattPointPackets.S2B000198
import PlattPointPackets.S2B000199
import PlattPointPackets.S2B000200
import PlattGlobalGrid.S7B000042
namespace ChenEffective.PlattWindow.PointCovers.S7B000042
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000196.points ++ ChenEffective.PlattWindow.PointPackets.S2B000197.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000198.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000199.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000200.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000042.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000042.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000042
