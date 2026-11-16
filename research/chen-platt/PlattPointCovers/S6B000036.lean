import PlattPointSubsetKernel
import PlattPointPackets.S1B000398
import PlattPointPackets.S1B000399
import PlattPointPackets.S1B000400
import PlattPointPackets.S1B000401
import PlattGlobalGrid.S6B000036
namespace ChenEffective.PlattWindow.PointCovers.S6B000036
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000398.points ++ ChenEffective.PlattWindow.PointPackets.S1B000399.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000400.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000401.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000036.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000036.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000036
