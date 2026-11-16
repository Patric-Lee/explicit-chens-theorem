import PlattPointSubsetKernel
import PlattPointPackets.S2B000037
import PlattPointPackets.S2B000038
import PlattPointPackets.S2B000039
import PlattPointPackets.S2B000040
import PlattGlobalGrid.S6B000113
namespace ChenEffective.PlattWindow.PointCovers.S6B000113
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000037.points ++ ChenEffective.PlattWindow.PointPackets.S2B000038.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000040.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000113.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000113.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000113
