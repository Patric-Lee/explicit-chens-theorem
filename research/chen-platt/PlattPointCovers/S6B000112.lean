import PlattPointSubsetKernel
import PlattPointPackets.S2B000034
import PlattPointPackets.S2B000035
import PlattPointPackets.S2B000036
import PlattPointPackets.S2B000037
import PlattGlobalGrid.S6B000112
namespace ChenEffective.PlattWindow.PointCovers.S6B000112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000034.points ++ ChenEffective.PlattWindow.PointPackets.S2B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000036.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000037.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000112.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000112.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000112
