import PlattPointSubsetKernel
import PlattPointPackets.S1B000401
import PlattPointPackets.S1B000402
import PlattPointPackets.S1B000403
import PlattPointPackets.S1B000404
import PlattGlobalGrid.S6B000037
namespace ChenEffective.PlattWindow.PointCovers.S6B000037
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000401.points ++ ChenEffective.PlattWindow.PointPackets.S1B000402.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000403.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000404.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000037.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000037.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000037
