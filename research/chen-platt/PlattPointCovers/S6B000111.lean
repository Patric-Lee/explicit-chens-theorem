import PlattPointSubsetKernel
import PlattPointPackets.S2B000031
import PlattPointPackets.S2B000032
import PlattPointPackets.S2B000033
import PlattPointPackets.S2B000034
import PlattGlobalGrid.S6B000111
namespace ChenEffective.PlattWindow.PointCovers.S6B000111
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000031.points ++ ChenEffective.PlattWindow.PointPackets.S2B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000033.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000034.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000111.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000111.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000111
