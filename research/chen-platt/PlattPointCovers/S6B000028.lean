import PlattPointSubsetKernel
import PlattPointPackets.S1B000375
import PlattPointPackets.S1B000376
import PlattPointPackets.S1B000377
import PlattPointPackets.S1B000378
import PlattGlobalGrid.S6B000028
namespace ChenEffective.PlattWindow.PointCovers.S6B000028
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000375.points ++ ChenEffective.PlattWindow.PointPackets.S1B000376.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000377.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000378.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000028.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000028.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000028
