import PlattPointSubsetKernel
import PlattPointPackets.S1B000312
import PlattPointPackets.S1B000313
import PlattPointPackets.S1B000314
import PlattPointPackets.S1B000315
import PlattGlobalGrid.S6B000004
namespace ChenEffective.PlattWindow.PointCovers.S6B000004
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000312.points ++ ChenEffective.PlattWindow.PointPackets.S1B000313.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000314.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000315.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000004.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000004.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000004
