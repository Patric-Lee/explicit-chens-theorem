import PlattPointSubsetKernel
import PlattPointPackets.S1B000433
import PlattPointPackets.S1B000434
import PlattPointPackets.S1B000435
import PlattPointPackets.S1B000436
import PlattPointPackets.S1B000437
import PlattGlobalGrid.S6B000047
namespace ChenEffective.PlattWindow.PointCovers.S6B000047
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000433.points ++ ChenEffective.PlattWindow.PointPackets.S1B000434.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000435.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000436.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000437.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000047.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000047.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000047
