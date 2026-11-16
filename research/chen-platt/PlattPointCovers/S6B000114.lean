import PlattPointSubsetKernel
import PlattPointPackets.S2B000040
import PlattPointPackets.S2B000041
import PlattPointPackets.S2B000042
import PlattPointPackets.S2B000043
import PlattGlobalGrid.S6B000114
namespace ChenEffective.PlattWindow.PointCovers.S6B000114
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000040.points ++ ChenEffective.PlattWindow.PointPackets.S2B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000043.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000114.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000114.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000114
