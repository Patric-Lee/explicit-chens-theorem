import PlattPointSubsetKernel
import PlattPointPackets.S1B000358
import PlattPointPackets.S1B000359
import PlattPointPackets.S1B000360
import PlattPointPackets.S1B000361
import PlattGlobalGrid.S6B000022
namespace ChenEffective.PlattWindow.PointCovers.S6B000022
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000358.points ++ ChenEffective.PlattWindow.PointPackets.S1B000359.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000360.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000361.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000022.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000022.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000022
