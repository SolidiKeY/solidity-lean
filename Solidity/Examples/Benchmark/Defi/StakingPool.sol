// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract StakingRewards {
    IERC20 public immutable stakingToken;
    IERC20 public immutable rewardsToken;

    address public owner;

    // Duration of rewards to be paid out (in seconds)
    uint256 public duration;
    // Timestamp of when the rewards finish
    uint256 public finishAt;
    // Minimum of last updated time and reward finish time
    uint256 public updatedAt;
    // Reward to be paid out per second
    uint256 public rewardRate;
    // Sum of (reward rate * dt * 1e18 / total supply)
    uint256 public rewardPerTokenStored;
    // User address => rewardPerTokenStored
    mapping(address => uint256) public userRewardPerTokenPaid;
    // User address => rewards to be claimed
    mapping(address => uint256) public rewards;

    // Total staked
    uint256 public totalSupply;
    // User address => staked amount
    mapping(address => uint256) public balanceOf;

    /// @custom:key ensures owner == msg.sender && stakingToken == _stakingToken && rewardsToken == _rewardToken
    /// @custom:key ensures duration == 0 && finishAt == 0 && updatedAt == 0 && rewardRate == 0 && rewardPerTokenStored == 0 && totalSupply == 0
    /// @custom:key ensures \forall address a; balanceOf[a] == 0 && rewards[a] == 0 && userRewardPerTokenPaid[a] == 0
    constructor(address _stakingToken, address _rewardToken) {
        owner = msg.sender;
        stakingToken = IERC20(_stakingToken);
        rewardsToken = IERC20(_rewardToken);
    }

    modifier onlyOwner() {
        require(msg.sender == owner, "not authorized");
        _;
    }

    modifier updateReward(address _account) {
        rewardPerTokenStored = rewardPerToken();
        updatedAt = lastTimeRewardApplicable();

        if (_account != address(0)) {
            rewards[_account] = earned(_account);
            userRewardPerTokenPaid[_account] = rewardPerTokenStored;
        }

        _;
    }

    /// @custom:key ensures finishAt <= block.timestamp -> \result == finishAt
    /// @custom:key ensures finishAt > block.timestamp -> \result == block.timestamp
    function lastTimeRewardApplicable() public view returns (uint256) {
        return _min(finishAt, block.timestamp);
    }

    /// @custom:key ensures totalSupply == 0 -> \result == rewardPerTokenStored
    /// @custom:key ensures totalSupply > 0 && finishAt <= block.timestamp -> \result == rewardPerTokenStored + rewardRate * (finishAt - updatedAt) * 1000000000000000000 / totalSupply
    /// @custom:key ensures totalSupply > 0 && finishAt > block.timestamp -> \result == rewardPerTokenStored + rewardRate * (block.timestamp - updatedAt) * 1000000000000000000 / totalSupply
    function rewardPerToken() public view returns (uint256) {
        if (totalSupply == 0) {
            return rewardPerTokenStored;
        }

        return rewardPerTokenStored
            + (rewardRate * (lastTimeRewardApplicable() - updatedAt) * 1e18)
                / totalSupply;
    }

    /// @custom:key ensures balanceOf[msg.sender] == \old(balanceOf[msg.sender]) + _amount
    /// @custom:key ensures totalSupply == \old(totalSupply) + _amount
    /// @custom:key ensures userRewardPerTokenPaid[msg.sender] == rewardPerTokenStored
    /// @custom:key ensures rewards[msg.sender] == \old(rewards[msg.sender]) + \old(balanceOf[msg.sender]) * (rewardPerTokenStored - \old(userRewardPerTokenPaid[msg.sender])) / 1000000000000000000
    /// @custom:key ensures updatedAt <= finishAt && updatedAt <= block.timestamp
    function stake(uint256 _amount) external updateReward(msg.sender) {
        require(_amount > 0, "amount = 0");
        stakingToken.transferFrom(msg.sender, address(this), _amount);
        balanceOf[msg.sender] += _amount;
        totalSupply += _amount;
    }

    /// @custom:key ensures balanceOf[msg.sender] == \old(balanceOf[msg.sender]) - _amount
    /// @custom:key ensures totalSupply == \old(totalSupply) - _amount
    /// @custom:key ensures userRewardPerTokenPaid[msg.sender] == rewardPerTokenStored
    /// @custom:key ensures rewards[msg.sender] == \old(rewards[msg.sender]) + \old(balanceOf[msg.sender]) * (rewardPerTokenStored - \old(userRewardPerTokenPaid[msg.sender])) / 1000000000000000000
    /// @custom:key ensures updatedAt <= finishAt && updatedAt <= block.timestamp
    function withdraw(uint256 _amount) external updateReward(msg.sender) {
        require(_amount > 0, "amount = 0");
        balanceOf[msg.sender] -= _amount;
        totalSupply -= _amount;
        stakingToken.transfer(msg.sender, _amount);
    }

    /// @custom:key ensures totalSupply == 0 -> \result == balanceOf[_account] * (rewardPerTokenStored - userRewardPerTokenPaid[_account]) / 1000000000000000000 + rewards[_account]
    /// @custom:key ensures totalSupply > 0 && finishAt <= block.timestamp -> \result == balanceOf[_account] * (rewardPerTokenStored + rewardRate * (finishAt - updatedAt) * 1000000000000000000 / totalSupply - userRewardPerTokenPaid[_account]) / 1000000000000000000 + rewards[_account]
    /// @custom:key ensures totalSupply > 0 && finishAt > block.timestamp -> \result == balanceOf[_account] * (rewardPerTokenStored + rewardRate * (block.timestamp - updatedAt) * 1000000000000000000 / totalSupply - userRewardPerTokenPaid[_account]) / 1000000000000000000 + rewards[_account]
    function earned(address _account) public view returns (uint256) {
        return (
            (
                balanceOf[_account]
                    * (rewardPerToken() - userRewardPerTokenPaid[_account])
            ) / 1e18
        ) + rewards[_account];
    }

    /// @custom:key ensures rewards[msg.sender] == 0
    /// @custom:key ensures userRewardPerTokenPaid[msg.sender] == rewardPerTokenStored
    /// @custom:key ensures balanceOf[msg.sender] == \old(balanceOf[msg.sender]) && totalSupply == \old(totalSupply)
    function getReward() external updateReward(msg.sender) {
        uint256 reward = rewards[msg.sender];
        if (reward > 0) {
            rewards[msg.sender] = 0;
            rewardsToken.transfer(msg.sender, reward);
        }
    }

    /// @custom:key ensures duration == _duration
    /// @custom:key ensures owner == \old(owner) && finishAt == \old(finishAt) && rewardRate == \old(rewardRate)
    function setRewardsDuration(uint256 _duration) external onlyOwner {
        require(finishAt < block.timestamp, "reward duration not finished");
        duration = _duration;
    }

    /// @custom:key ensures finishAt == block.timestamp + duration && updatedAt == block.timestamp
    /// @custom:key ensures block.timestamp >= \old(finishAt) -> rewardRate == _amount / duration
    /// @custom:key ensures block.timestamp < \old(finishAt) -> rewardRate == (_amount + (\old(finishAt) - block.timestamp) * \old(rewardRate)) / duration
    /// @custom:key ensures owner == \old(owner) && totalSupply == \old(totalSupply)
    function notifyRewardAmount(uint256 _amount)
        external
        onlyOwner
        updateReward(address(0))
    {
        if (block.timestamp >= finishAt) {
            rewardRate = _amount / duration;
        } else {
            uint256 remainingRewards = (finishAt - block.timestamp) * rewardRate;
            rewardRate = (_amount + remainingRewards) / duration;
        }

        require(rewardRate > 0, "reward rate = 0");
        require(
            rewardRate * duration <= rewardsToken.balanceOf(address(this)),
            "reward amount > balance"
        );

        finishAt = block.timestamp + duration;
        updatedAt = block.timestamp;
    }

    /// @custom:key ensures x <= y -> \result == x
    /// @custom:key ensures x > y -> \result == y
    function _min(uint256 x, uint256 y) private pure returns (uint256) {
        return x <= y ? x : y;
    }
}

interface IERC20 {
    function totalSupply() external view returns (uint256);
    function balanceOf(address account) external view returns (uint256);
    function transfer(address recipient, uint256 amount)
        external
        returns (bool);
    function allowance(address owner, address spender)
        external
        view
        returns (uint256);
    function approve(address spender, uint256 amount) external returns (bool);
    function transferFrom(address sender, address recipient, uint256 amount)
        external
        returns (bool);
}
