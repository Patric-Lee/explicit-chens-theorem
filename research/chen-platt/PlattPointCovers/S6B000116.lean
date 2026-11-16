import PlattPointSubsetKernel
import PlattPointPackets.S2B000046
import PlattPointPackets.S2B000047
import PlattPointPackets.S2B000048
import PlattPointPackets.S2B000049
import PlattGlobalGrid.S6B000116
namespace ChenEffective.PlattWindow.PointCovers.S6B000116
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000046.points ++ ChenEffective.PlattWindow.PointPackets.S2B000047.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000048.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000049.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000116.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000116.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000116
