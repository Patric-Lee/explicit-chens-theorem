import PlattPointSubsetKernel
import PlattPointPackets.S2B000043
import PlattPointPackets.S2B000044
import PlattPointPackets.S2B000045
import PlattPointPackets.S2B000046
import PlattGlobalGrid.S6B000115
namespace ChenEffective.PlattWindow.PointCovers.S6B000115
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000043.points ++ ChenEffective.PlattWindow.PointPackets.S2B000044.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000046.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000115.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000115.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000115
