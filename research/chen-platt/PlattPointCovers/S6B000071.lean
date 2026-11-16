import PlattPointSubsetKernel
import PlattPointPackets.S1B000521
import PlattPointPackets.S1B000522
import PlattPointPackets.S1B000523
import PlattPointPackets.S1B000524
import PlattPointPackets.S1B000525
import PlattGlobalGrid.S6B000071
namespace ChenEffective.PlattWindow.PointCovers.S6B000071
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000521.points ++ ChenEffective.PlattWindow.PointPackets.S1B000522.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000523.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000524.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000525.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000071.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000071.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000071
