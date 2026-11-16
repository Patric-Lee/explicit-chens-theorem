import PlattPointSubsetKernel
import PlattPointPackets.S1B000437
import PlattPointPackets.S1B000438
import PlattPointPackets.S1B000439
import PlattPointPackets.S1B000440
import PlattGlobalGrid.S6B000048
namespace ChenEffective.PlattWindow.PointCovers.S6B000048
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000437.points ++ ChenEffective.PlattWindow.PointPackets.S1B000438.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000439.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000440.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000048.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000048.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000048
